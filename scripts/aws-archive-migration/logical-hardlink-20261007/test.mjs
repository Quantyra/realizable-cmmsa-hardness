import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { randomBytes, createCipheriv } from 'node:crypto';
import { gzipSync } from 'node:zlib';
import { Readable } from 'node:stream';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import tar from 'tar-stream';
import { sha } from '../archive.mjs';
import { DEST } from '../migrate.mjs';
import { restore, selection, plan } from './restore.mjs';
import { authorize, authorizeRoute } from './authorization.mjs';
import { directoryWrapper } from './wrappers.mjs';
const fragments = b => Readable.from(Array.from({length:Math.ceil(b.length/31)},(_,i)=>b.subarray(i*31,i*31+31)));
async function fixture({same=false,chain=true,size=23,tarFault,extra=false}={}) {
  const key=randomBytes(32),data=Buffer.alloc(size,97),content={path:'archive/cmmsa44-objects/'+sha(data),bytes:data.length,sha256:sha(data),chunk:1};
  const middle={path:'archive/middle',bytes:data.length,sha256:sha(data),chunk:same?1:2,hardlink:content.path};
  const logical={path:'realizable-cmmsa-hardness/evidence/fixture/check.rc',bytes:data.length,sha256:sha(data),chunk:same?1:chain?3:2,hardlink:chain?middle.path:content.path};
  const extraData=Buffer.alloc(37,98),extraContent={path:'archive/cmmsa44-objects/'+sha(extraData),bytes:extraData.length,sha256:sha(extraData),chunk:1},extraLogical={path:'realizable-cmmsa-hardness/evidence/fixture/other.rc',bytes:extraData.length,sha256:sha(extraData),chunk:logical.chunk,hardlink:extraContent.path};
  const members=[content,...chain?[middle]:[],logical,...extra?[extraContent,extraLogical]:[]],envelopes=new Map(),chunks=[];
  for(const number of [...new Set(members.map(m=>m.chunk))]) {
    const pack=tar.pack(),parts=[],collect=(async()=>{for await(const b of pack)parts.push(b);})();
    for(const m of members.filter(m=>m.chunk===number)) {
      if(tarFault==='missing-logical'&&m===logical)continue;
      if(m.hardlink!=null)pack.entry({name:m.path,type:tarFault==='symlink'&&m===logical?'symlink':'link',linkname:tarFault==='wrong-link'&&m===logical?'archive/foreign':m.hardlink,size:0});
      else {const bytes=m===extraContent?extraData:data;pack.entry({name:m.path,size:bytes.length},bytes);}
    }
    pack.finalize();await collect;const plain=gzipSync(Buffer.concat(parts)),nonce=randomBytes(12),cipher=createCipheriv('aes-256-gcm',key,nonce);
    const bytes=Buffer.concat([Buffer.from('QARC1'),nonce,cipher.update(plain),cipher.final(),cipher.getAuthTag()]);
    const chunk={number,key:'synthetic-'+number,version_id:'exact-'+number,bytes:bytes.length,sha256:sha(bytes),tar_sha256:sha(plain)};chunks.push(chunk);envelopes.set(chunk.key,bytes);
  }
  return {key,data,content,logical,middle,extraData,extraContent,extraLogical,envelopes,c:{bucket:DEST,profile:'quantyra',selected_directory:'realizable-cmmsa-hardness/evidence/fixture',chunks,members}};
}
async function withFixture(options,run) {
  const f=await fixture(options),dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-logical-test-')),root=path.join(dir,'root'),catalog=path.join(dir,'catalog.json'),keyFile=path.join(dir,'synthetic-key');
  try {
    await fs.mkdir(root);await fs.writeFile(catalog,JSON.stringify(f.c));await fs.writeFile(keyFile,f.key);
    const calls=[],client={send:async cmd=>{assert.equal(cmd.constructor.name,'GetObjectCommand');assert.equal(cmd.input.Bucket,DEST);assert.equal(cmd.input.ExpectedBucketOwner,'063280428495');const chunk=f.c.chunks.find(x=>x.key===cmd.input.Key);assert.equal(cmd.input.VersionId,chunk.version_id);calls.push(cmd.input.Key);return {Body:fragments(f.envelopes.get(cmd.input.Key))};}};
    await run({...f,dir,root,catalog,keyFile,calls,client,o:{catalog,keyFile,workspaceRoot:root,path:f.logical.path}});
  } finally {
    f.key.fill(0);assert.equal(path.dirname(dir),await fs.realpath(os.tmpdir()));assert(path.basename(dir).startsWith('qarc-logical-test-'));await fs.rm(dir,{recursive:true,force:true});
  }
}
test('multi-chunk multi-hop logical reference becomes one independent regular file at logical path',()=>withFixture({},async f=>{
  const r=await restore(f.o,f.client),output=path.join(f.root,f.logical.path),s=await fs.lstat(output);
  assert(s.isFile()&&!s.isSymbolicLink());assert.equal(s.nlink,1);assert.deepEqual(await fs.readFile(output),f.data);assert.equal(r.chunks,3);assert.equal(r.hardlink_depth,2);assert.equal(r.logical_member_kind,'hardlink');assert.equal(r.materialized_kind,'regular');
  assert.equal(r.member_metadata_sha256,sha(Buffer.from(JSON.stringify(f.logical))));assert.equal(r.content_member_metadata_sha256,sha(Buffer.from(JSON.stringify(f.content))));assert.equal(r.catalog_sha256,sha(await fs.readFile(f.catalog)));assert.deepEqual(r.exact_versions.map(x=>x.version_id),['exact-1','exact-2','exact-3']);
  await assert.rejects(fs.stat(path.join(f.root,f.content.path)),{code:'ENOENT'});assert(!((await fs.readdir(f.root)).some(x=>x.startsWith('.qarc-'))));
  await assert.rejects(restore(f.o,f.client),/Refusing existing/);assert.equal(f.calls.length,3);
}));
test('same-chunk logical reference is staged from regular bytes and authenticated with tar order',()=>withFixture({same:true},async f=>{const r=await restore(f.o,f.client);assert.equal(r.chunks,1);assert.equal(r.hardlink_depth,2);assert.deepEqual(await fs.readFile(path.join(f.root,f.logical.path)),f.data);}));
test('regular selection remains supported',()=>withFixture({},async f=>{const r=await restore({...f.o,path:f.content.path},f.client);assert.equal(r.logical_member_kind,'regular');assert.equal(r.hardlink_depth,0);assert.equal(r.chunks,1);}));
test('multiple selections and directory prefixes stage distinct content once per chunk and deduplicate overlaps',()=>withFixture({same:true,chain:false,extra:true},async f=>{
  const r=await restore({...f.o,path:undefined,paths:['realizable-cmmsa-hardness/evidence/fixture',f.logical.path,f.extraLogical.path]},f.client);assert.equal(r.members,2);assert.equal(r.bytes,f.data.length+f.extraData.length);assert.equal(f.calls.length,1);assert.equal(r.outputs.length,2);assert.deepEqual(await fs.readFile(path.join(f.root,f.logical.path)),f.data);assert.deepEqual(await fs.readFile(path.join(f.root,f.extraLogical.path)),f.extraData);await assert.rejects(fs.stat(path.join(f.root,f.content.path)),{code:'ENOENT'});
}));
test('no selectors restores the full synthetic catalog scope including logical references',()=>withFixture({same:true,chain:false,extra:true},async f=>{
  const r=await restore({...f.o,path:undefined},f.client);assert.equal(r.members,4);assert.equal(f.calls.length,1);for(const name of [f.content.path,f.logical.path,f.extraContent.path,f.extraLogical.path])assert((await fs.lstat(path.join(f.root,name))).isFile());
}));
test('production restores a member larger than 1 MiB while explicit bounded mode refuses it',()=>withFixture({size:1048577,chain:false},async f=>{
  await assert.rejects(restore({...f.o,bounded:true},f.client),/bounded/);assert.equal(f.calls.length,0);const r=await restore(f.o,f.client);assert.equal(r.bytes,1048577);assert.equal((await fs.stat(path.join(f.root,f.logical.path))).size,1048577);
}));
test('disk preflight and protected existing output reject the entire selection before key/client access',()=>withFixture({same:true,chain:false,extra:true},async f=>{
  const options={...f.o,path:undefined,paths:['realizable-cmmsa-hardness/evidence/fixture'],keyFile:path.join(f.dir,'missing-key')};
  const budget=plan(f.c,options.paths).requiredDiskBytes;assert(budget>BigInt(2*(f.data.length+f.extraData.length)));await assert.rejects(restore(options,f.client,{freeBytes:async()=>budget-1n}),/Insufficient disk/);assert.equal(f.calls.length,0);assert.deepEqual(await fs.readdir(f.root),[]);
  const existing=path.join(f.root,f.extraLogical.path);await fs.mkdir(path.dirname(existing),{recursive:true});await fs.writeFile(existing,'protected original');await assert.rejects(restore(options,f.client),/Refusing existing/);assert.equal(f.calls.length,0);assert.equal(await fs.readFile(existing,'utf8'),'protected original');await assert.rejects(fs.stat(path.join(f.root,f.logical.path)),{code:'ENOENT'});
}));
test('late authentication failure in a multi-file selection publishes nothing',()=>withFixture({chain:false,extra:true},async f=>{
  const name=f.c.chunks.at(-1).key,b=Buffer.from(f.envelopes.get(name));b[b.length-1]^=1;f.envelopes.set(name,b);await assert.rejects(restore({...f.o,path:undefined,paths:['realizable-cmmsa-hardness/evidence/fixture']},f.client));assert.deepEqual(await fs.readdir(f.root),[]);
}));
test('exact 1 MiB logical output passes and larger output fails before I/O',()=>withFixture({size:1048576,chain:false},async f=>{assert.equal((await restore(f.o,f.client)).bytes,1048576);const c=structuredClone(f.c);for(const m of c.members)m.bytes++;assert.throws(()=>selection(c,f.logical.path),/bounded/);}));
for(const failure of ['content-tag','logical-tag','wrong-link','missing-logical','symlink','member-hash']) {
  test(failure+' cannot publish logical output and removes staging',()=>withFixture({tarFault:failure},async f=>{
    if(failure.endsWith('-tag')){const name=failure==='content-tag'?f.c.chunks[0].key:f.c.chunks.at(-1).key;const b=Buffer.from(f.envelopes.get(name));b[b.length-1]^=1;f.envelopes.set(name,b);}
    if(failure==='member-hash'){for(const m of f.c.members)m.sha256='0'.repeat(64);await fs.writeFile(f.catalog,JSON.stringify(f.c));}
    await assert.rejects(restore(f.o,f.client));await assert.rejects(fs.stat(path.join(f.root,f.logical.path)),{code:'ENOENT'});assert.deepEqual(await fs.readdir(f.root),[]);
  }));
}
test('catalog graph, metadata, unsafe paths and collisions reject before key/client operations',()=>withFixture({},async f=>{
  const changes=[c=>c.members[2].path='realizable-cmmsa-hardness/../escape',c=>c.members[2].path='realizable-cmmsa-hardness/CON',c=>c.members[1].hardlink='archive/missing',c=>c.members[1].hardlink='C:/external/private',c=>c.members[0].hardlink=c.members[1].path,c=>c.members[2].sha256='0'.repeat(64),c=>c.members[2].bytes++,c=>c.members.push({...c.members[2],path:c.members[2].path.toUpperCase()}),c=>c.members.push({...c.members[0],path:'realizable-cmmsa-hardness/evidence'})];
  for(const change of changes){const c=structuredClone(f.c);change(c);await fs.writeFile(f.catalog,JSON.stringify(c));await assert.rejects(restore({...f.o,keyFile:path.join(f.dir,'nonexistent')},f.client));}assert.equal(f.calls.length,0);
}));
test('junction ancestor and non-directory ancestor reject without contacting client',()=>withFixture({},async f=>{
  const outside=path.join(f.dir,'outside');await fs.mkdir(outside);const ancestor=path.join(f.root,'realizable-cmmsa-hardness');await fs.symlink(outside,ancestor,process.platform==='win32'?'junction':'dir');await assert.rejects(restore(f.o,f.client),/Unsafe output/);assert.equal(f.calls.length,0);assert.deepEqual(await fs.readdir(outside),[]);await fs.unlink(ancestor);await fs.writeFile(ancestor,'synthetic obstruction');await assert.rejects(restore(f.o,f.client),/Unsafe output/);assert.equal(f.calls.length,0);
}));
test('new independent acceptance is required; altered bindings and stale authorization reject',()=>{
  const h='a'.repeat(64),reviewHash='b'.repeat(64),commit='c'.repeat(40),old='6bdf7532fb020397a5cf60c0bf7cc2afccb4cbac';
  const s={type:'archive-logical-hardlink-code-supplement-v1',fresh_archive_authentication:false,data_versions_unchanged:true,old_packet_sha256:h,code_commit:commit,old_root_acceptance_commit:old};
  const a={type:'archive-logical-hardlink-root-acceptance-v1',decision:'ACCEPT',reviewer_role:'root-independent-verifier',author_proof_is_not_independent:true,code_supplement_sha256:h,independent_verification_sha256:reviewHash,old_packet_sha256:h,code_commit:commit,old_root_acceptance_commit:old};
  const r={type:'archive-logical-hardlink-independent-verification-v1',complete:true,reviewer_role:'independent-code-verifier',verdict:'GO-WITH-BOUNDARIES',code_supplement_sha256:h,old_packet_sha256:h,code_commit:commit};
  assert.doesNotThrow(()=>authorize(s,a,r,h,reviewHash));
  for(const [x,y,z] of [[s,{...a,type:'archive-root-acceptance-v1'},r],[s,{...a,decision:'HOLD'},r],[s,a,{...r,complete:false}],[s,a,{...r,reviewer_role:'author'}],[s,a,{...r,old_packet_sha256:reviewHash}],[s,{...a,code_commit:'d'.repeat(40)},r],[{...s,fresh_archive_authentication:true},a,r]])assert.throws(()=>authorize(x,y,z,h,reviewHash));
  assert.throws(()=>authorize(s,a,r,h,h));
});
test('recovery scope is catalog-bound and raw content-addressed bypass rejects',()=>withFixture({},async f=>{
  const pin={directory:44},entry={directory:44,selected_directory:'evidence/fixture'};assert.doesNotThrow(()=>authorizeRoute(pin,entry,f.c,f.logical.path,false));assert.throws(()=>authorizeRoute(pin,entry,f.c,f.content.path,false));assert.throws(()=>authorizeRoute(pin,{...entry,selected_directory:'archive'},f.c,f.content.path,false));assert.throws(()=>authorizeRoute(pin,entry,f.c,f.logical.path,true));
}));
test('successor entry refuses the old synthetic registry before credentials or archive access',()=>withFixture({},async f=>{
  const state=path.join(f.dir,'.quantyra/aws-migration-20261006');await fs.mkdir(state,{recursive:true});await fs.writeFile(path.join(state,'active-restore-registry.json'),JSON.stringify({status:'verified-quantyra-archive-migration',core:{catalog_file:f.catalog},recovery:[]}));
  const r=spawnSync(process.execPath,[fileURLToPath(new URL('./active-restore.mjs',import.meta.url)),'--dry-run'],{env:{...process.env,USERPROFILE:f.dir,HOME:f.dir},windowsHide:true,encoding:'utf8'});assert.equal(r.status,1);assert.equal(r.stdout,'');assert(r.stderr.includes('Accepted bounded logical restore failed'));
}));
test('successor installer refuses the old acceptance commit before any local installation write',()=>withFixture({},async f=>{
  const before=(await fs.readdir(f.dir)).sort();
  const r=spawnSync(process.execPath,[fileURLToPath(new URL('./install-local-restore.mjs',import.meta.url)),'--root-acceptance-commit','6bdf7532fb020397a5cf60c0bf7cc2afccb4cbac'],{env:{...process.env,USERPROFILE:f.dir,HOME:f.dir},windowsHide:true,encoding:'utf8'});
  assert.equal(r.status,1);assert.equal(r.stdout,'');assert.equal(JSON.parse(r.stderr.trim()).status,'installation-failed');assert.deepEqual((await fs.readdir(f.dir)).sort(),before);
}));
test('actual generated PowerShell route materializes a synthetic logical reference and refuses traversal/outside selection', {skip:process.platform!=='win32'},()=>withFixture({chain:false},async f=>{
  const state=path.join(f.dir,'.quantyra/aws-migration-20261006'),bin=path.join(f.dir,'.local/bin'),psDir=path.join(f.dir,'ps');await fs.mkdir(state,{recursive:true});await fs.mkdir(bin,{recursive:true});await fs.mkdir(psDir);
  await fs.writeFile(path.join(state,'active-restore-registry.json'),JSON.stringify({status:'verified-quantyra-archive-migration',recovery:[{directory:44,catalog_file:f.catalog,catalog_sha256:sha(await fs.readFile(f.catalog)),selected_directory:'evidence/fixture'}]}));
  const envelopeFiles={};for(const [k,b] of f.envelopes){const file=path.join(f.dir,k+'.bin');await fs.writeFile(file,b);envelopeFiles[k]=file;}
  const driver=`import fs from 'node:fs/promises';import {Readable} from 'node:stream';import {restore} from ${JSON.stringify(new URL('./restore.mjs',import.meta.url).href)};const args=process.argv.slice(2),get=k=>args[args.indexOf(k)+1];const bodies=${JSON.stringify(envelopeFiles)};const r=await restore({catalog:get('--catalog'),workspaceRoot:get('--workspace-root'),path:get('--path'),bounded:args.includes('--bounded'),keyFile:${JSON.stringify(f.keyFile)}},{send:async c=>({Body:Readable.from([await fs.readFile(bodies[c.input.Key])])})});console.log(JSON.stringify(r));`;
  await fs.writeFile(path.join(bin,'restore-quantyra-archive.mjs'),driver);const ps=path.join(psDir,'restore-directory.ps1');await fs.writeFile(ps,directoryWrapper());
  const invoke=(file,bounded=false)=>spawnSync('powershell.exe',['-NoProfile','-NonInteractive','-File',ps,'-DirectoryNumber','44','-Mode','Restore','-RelativeFile',file,...bounded?['-Bounded']:[]],{env:{...process.env,USERPROFILE:f.dir},windowsHide:true,encoding:'utf8',timeout:30000});
  const r=invoke(f.logical.path.replace(/^realizable-cmmsa-hardness\//,''));assert.equal(r.status,0,r.stderr);const receipt=JSON.parse(r.stdout.trim().split(/\r?\n/)[0]);assert.equal(receipt.logical_member_kind,'hardlink');assert.equal(receipt.sha256,sha(f.data));const outputs=(await fs.readdir(psDir)).filter(x=>x.startsWith('restore-quantyra-'));assert.equal(outputs.length,1);assert.deepEqual(await fs.readFile(path.join(psDir,outputs[0],f.logical.path)),f.data);
  const bounded=invoke(f.logical.path.replace(/^realizable-cmmsa-hardness\//,''),true);assert.equal(bounded.status,0,bounded.stderr);
  for(const file of ['evidence/fixture/../escape','archive/outside','evidence/fixture/a\\b']){const bad=invoke(file);assert.notEqual(bad.status,0);assert(!bad.stdout.includes('"mode":"restored"'));}assert.equal((await fs.readdir(psDir)).filter(x=>x.startsWith('restore-quantyra-')).length,2);
  const prefix=invoke('evidence/fixture');assert.equal(prefix.status,0,prefix.stderr);const full=spawnSync('powershell.exe',['-NoProfile','-NonInteractive','-File',ps,'-DirectoryNumber','44','-Mode','Restore'],{env:{...process.env,USERPROFILE:f.dir},windowsHide:true,encoding:'utf8',timeout:30000});assert.equal(full.status,0,full.stderr);assert.equal(JSON.parse(full.stdout.trim().split(/\r?\n/)[0]).members,1);assert.equal((await fs.readdir(psDir)).filter(x=>x.startsWith('restore-quantyra-')).length,4);
}));
