import test from 'node:test';
import assert from 'node:assert/strict';
import { randomBytes, createCipheriv } from 'node:crypto';
import { Readable } from 'node:stream';
import { gzipSync } from 'node:zlib';
import * as fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import tar from 'tar-stream';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { sha, validate, verifyChunk } from './archive.mjs';
import { inventory, transfer, successor, successorCompatible, orderedRows, transferMarker, SOURCE, DEST } from './migrate.mjs';
import { restore } from './restore.mjs';
import { samePolicy } from './policy.mjs';
import { verifyCached } from './verification-cache.mjs';
import { sameHeaders,sameTags } from './verify-version-mapping.mjs';

async function fixture() {
  const key=randomBytes(32),data=Buffer.from('archive custody fixture\n'),name='realizable-cmmsa-hardness/evidence/test.log';
  const pack=tar.pack(),parts=[];const collecting=(async()=>{for await(const b of pack)parts.push(b);})();
  pack.entry({name,size:data.length},data);pack.entry({name:'archive/hardlink.log',type:'link',linkname:name,size:0});pack.finalize();await collecting;
  const plain=gzipSync(Buffer.concat(parts)),nonce=randomBytes(12),cipher=createCipheriv('aes-256-gcm',key,nonce);
  const envelope=Buffer.concat([Buffer.from('QARC1'),nonce,cipher.update(plain),cipher.final(),cipher.getAuthTag()]);
  const chunk={number:1,key:'fixture.qarc',version_id:'old-v',bytes:envelope.length,sha256:sha(envelope),tar_sha256:sha(plain)};
  const c={bucket:SOURCE,profile:'cyint-ea-prod',chunks:[chunk],members:[{path:name,bytes:data.length,sha256:sha(data),chunk:1},{path:'archive/hardlink.log',bytes:data.length,sha256:sha(data),chunk:1,hardlink:name}]};
  return {key,data,name,envelope,chunk,c};
}
const fragmented=b=>Readable.from(Array.from({length:Math.ceil(b.length/7)},(_,i)=>b.subarray(i*7,i*7+7)));
test('stream authentication, every member hash and bounded actual restore',async()=>{
  const f=await fixture(),{members}=validate(f.c),verified=new Set(),dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-test-')),temp=path.join(dir,'selected');
  try { const r=await verifyChunk(fragmented(f.envelope),f.chunk,members,f.key,verified,{...f.c.members[0],temp});assert.equal(r.members,2);assert.equal(verified.size,2);assert.deepEqual(await fs.readFile(temp),f.data); }
  finally {f.key.fill(0);await fs.rm(dir,{recursive:true,force:true});}
});
test('bad tag removes unauthenticated restore and member receipts',async()=>{
  const f=await fixture(),bad=Buffer.from(f.envelope);bad[bad.length-1]^=1;
  const dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-test-')),temp=path.join(dir,'selected'),verified=new Set();
  try {await assert.rejects(verifyChunk(fragmented(bad),f.chunk,validate(f.c).members,f.key,verified,{...f.c.members[0],temp}));assert.equal(verified.size,0);await assert.rejects(fs.stat(temp),{code:'ENOENT'});}
  finally {f.key.fill(0);await fs.rm(dir,{recursive:true,force:true});}
});
test('member hash mismatch and missing catalog member fail closed',async()=>{
  const f=await fixture();f.c.members[0].sha256='0'.repeat(64);f.c.members[1].sha256='0'.repeat(64);
  await assert.rejects(verifyChunk(fragmented(f.envelope),f.chunk,validate(f.c).members,f.key,new Set()),/Member hash mismatch/);
  const g=await fixture();g.c.members.push({path:'archive/missing.log',bytes:0,sha256:sha(''),chunk:1});
  await assert.rejects(verifyChunk(fragmented(g.envelope),g.chunk,validate(g.c).members,g.key,new Set()),/Missing member/);f.key.fill(0);g.key.fill(0);
});
test('catalog rejects traversal, folded duplicates and hardlink cycles',async()=>{
  const f=await fixture();for(const name of ['archive/../bad','archive/CON','archive/a\\b']){const c=structuredClone(f.c);c.members[0].path=name;assert.throws(()=>validate(c));}
  const c=structuredClone(f.c);c.members.push({...c.members[0],path:c.members[0].path.toUpperCase()});assert.throws(()=>validate(c));
  f.c.members[0].hardlink=f.c.members[1].path;assert.throws(()=>validate(f.c),/Cyclic/);f.key.fill(0);
});
test('paged inventory includes historical versions and delete markers',async()=>{
  let calls=0;const client={send:async cmd=>{assert.equal(cmd.input.ExpectedBucketOwner,'485386182336');return calls++===0?{Versions:[{Key:'x',VersionId:'v2',Size:3}],IsTruncated:true,NextKeyMarker:'x',NextVersionIdMarker:'v2'}:{Versions:[{Key:'x',VersionId:'v1',Size:2}],DeleteMarkers:[{Key:'y',VersionId:'d1'}]};}};
  const r=await inventory(client,SOURCE,'485386182336');assert.equal(r.length,3);assert.equal(r[2].kind,'delete-marker');
});
test('multipart relay uses exact source version, destination owner and rereads ciphertext',async()=>{
  const data=randomBytes(9*1024**2),parts=[],calls=[];
  const s={send:async cmd=>{assert.equal(cmd.input.VersionId,'old');assert.equal(cmd.input.Bucket,SOURCE);switch(cmd.constructor.name){case 'HeadObjectCommand':return {ContentLength:data.length,ETag:'etag',Metadata:{fixture:'true'}};case 'GetObjectTaggingCommand':return {TagSet:[]};case 'GetObjectCommand':return {Body:Readable.from([data.subarray(0,123),data.subarray(123)])};default:throw Error('Unexpected source command');}}};
  const d={send:async cmd=>{calls.push(cmd.constructor.name);assert.equal(cmd.input.Bucket,DEST);assert.equal(cmd.input.ExpectedBucketOwner,'063280428495');switch(cmd.constructor.name){case 'CreateMultipartUploadCommand':return {UploadId:'upload'};case 'UploadPartCommand':parts.push(Buffer.from(cmd.input.Body));return {ETag:String(parts.length)};case 'CompleteMultipartUploadCommand':return {VersionId:'new'};case 'GetObjectCommand':assert.equal(cmd.input.VersionId,'new');return {Body:Readable.from(parts)};case 'HeadObjectCommand':return {Metadata:{fixture:'true'}};case 'GetObjectTaggingCommand':return {TagSet:[]};default:throw Error('Unexpected destination command');}}};
  const r=await transfer(s,d,{kind:'object',key:'fixture',version:'old',bytes:data.length,etag:'etag'});assert.equal(parts.length,2);assert.equal(r.sha256,sha(data));assert.equal(r.destination_version,'new');assert.equal(r.verified,true);assert(!calls.some(c=>c.startsWith('Delete')));
});
test('successor requires verified exact version and leaves historical bytes unchanged',async()=>{
  const f=await fixture(),before=JSON.stringify(f.c),mapping=[{kind:'object',key:f.chunk.key,version:'old-v',bytes:f.chunk.bytes,sha256:f.chunk.sha256,verified:true,destination_version:'new-v'}];
  const next=successor(f.c,mapping,sha(before));assert.equal(next.chunks[0].version_id,'new-v');assert.equal(next.chunks[0].source_version_id,'old-v');assert.equal(JSON.stringify(f.c),before);mapping[0].verified=false;assert.throws(()=>successor(f.c,mapping,sha(before)));f.key.fill(0);
});
test('historical replay orders markers and versions, refuses ambiguous chronology',async()=>{
  const rows=[{key:'x',version:'2',kind:'delete-marker',last_modified:'2026-01-02'},{key:'x',version:'1',kind:'object',last_modified:'2026-01-01'}];assert.equal(orderedRows(rows)[0].version,'1');
  assert.throws(()=>orderedRows([rows[0],{...rows[0],version:'3'}]),/Ambiguous/);
  const d={send:async cmd=>{assert.equal(cmd.constructor.name,'DeleteObjectCommand');assert.equal(cmd.input.Bucket,DEST);assert.equal(cmd.input.ExpectedBucketOwner,'063280428495');assert.equal(cmd.input.VersionId,undefined);return {DeleteMarker:true,VersionId:'new-marker'};}};
  assert.equal((await transferMarker(d,rows[0])).destination_version,'new-marker');
});
test('bounded restore verifies complete chunk, publishes exact member, refuses overwrite',async()=>{
  const f=await fixture(),dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-test-'));
  try {
    const catalog=path.join(dir,'catalog.json'),keyFile=path.join(dir,'key'),root=path.join(dir,'root');await fs.mkdir(root);await fs.writeFile(catalog,JSON.stringify(f.c));await fs.writeFile(keyFile,f.key);
    const client={send:async cmd=>{assert.equal(cmd.input.VersionId,'old-v');return {Body:fragmented(f.envelope)};}};
    const options={catalog,keyFile,workspaceRoot:root,path:f.name};const r=await restore(options,client);assert.equal(r.mode,'restored');assert.deepEqual(await fs.readFile(path.join(root,f.name)),f.data);await assert.rejects(restore(options,client),/Refusing existing/);
    assert.equal((await fs.readdir(root)).some(n=>n.startsWith('.qarc-restore-')),false);
  } finally {f.key.fill(0);await fs.rm(dir,{recursive:true,force:true});}
});
test('policy comparison accepts AWS singleton normalization and detects widened grants',()=>{
  const p={Version:'2012-10-17',Statement:[{Effect:'Allow',Principal:{AWS:'arn:fixture'},Action:['s3:PutObject'],Resource:'arn:bucket/prefix/*'}]};
  const normalized={Statement:[{Resource:['arn:bucket/prefix/*'],Action:'s3:PutObject',Principal:{AWS:['arn:fixture']},Effect:'Allow'}],Version:'2012-10-17'};
  assert(samePolicy(p,normalized));normalized.Statement[0].Resource=['*'];assert(!samePolicy(p,normalized));
});
test('verified core successor stays stable when an additional archive mapping arrives',async()=>{
  const f=await fixture(),m=[{kind:'object',key:f.chunk.key,version:'old-v',bytes:f.chunk.bytes,sha256:f.chunk.sha256,verified:true,destination_version:'new-v'}],old=successor(f.c,m,'source-hash');
  m.push({kind:'object',key:'additional',version:'old-other',destination_version:'new-other',verified:true});
  assert(successorCompatible(old,successor(f.c,m,'source-hash'),m));m[0].destination_version='wrong';assert(!successorCompatible(old,successor(f.c,m,'source-hash'),m));f.key.fill(0);
});
test('active consumer redirects historical catalogs to hash-pinned Quantyra successor',async()=>{
  const f=await fixture(),dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-test-'));
  try {
    const historical=path.join(dir,'old.json'),current=path.join(dir,'new.json'),state=path.join(dir,'.quantyra/aws-migration-20261006');await fs.mkdir(state,{recursive:true});
    const old=Buffer.from(JSON.stringify(f.c)),next=Buffer.from(JSON.stringify({...f.c,bucket:DEST,profile:'quantyra'}));await fs.writeFile(historical,old);await fs.writeFile(current,next);
    await fs.writeFile(path.join(state,'active-restore-registry.json'),JSON.stringify({status:'verified-quantyra-archive-migration',core:{catalog_file:current,source_catalog_sha256:sha(old),catalog_sha256:sha(next)},recovery:[]}));
    const script=fileURLToPath(new URL('./active-restore.mjs',import.meta.url)),args=[script,'--catalog',historical,'--profile','cyint-ea-prod','--dry-run'];
    const env={...process.env,USERPROFILE:dir};const r=spawnSync(process.execPath,args,{env,encoding:'utf8',windowsHide:true});assert.equal(r.status,0,r.stderr);assert.equal(JSON.parse(r.stdout).profile,'quantyra');assert.equal(JSON.parse(r.stdout).members,2);assert(!r.stdout.includes(f.name));
    await fs.writeFile(current,'{}');const bad=spawnSync(process.execPath,args,{env,encoding:'utf8',windowsHide:true});assert.equal(bad.status,1);assert(!bad.stdout);assert(!bad.stderr.includes(f.name));
  } finally {f.key.fill(0);await fs.rm(dir,{recursive:true,force:true});}
});
test('shared chunks reuse only identical version and complete member identities',async()=>{
  const f=await fixture(),dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-test-')),cache=new Map();let calls=0;
  try {
    const keyFile=path.join(dir,'key');await fs.writeFile(keyFile,f.key);
    const client={send:async()=>{calls++;return {Body:fragmented(f.envelope)};}};
    const one=await verifyCached(client,f.c,keyFile,path.join(dir,'one'),cache),two=await verifyCached(client,f.c,keyFile,path.join(dir,'two'),cache);assert.equal(one.streamed_chunks,1);assert.equal(two.reused_chunks,1);assert.equal(calls,1);
    const changed=structuredClone(f.c);changed.members[0].sha256='0'.repeat(64);changed.members[1].sha256='0'.repeat(64);await assert.rejects(verifyCached(client,changed,keyFile,path.join(dir,'changed'),cache));assert.equal(calls,2);
    const newVersion=structuredClone(f.c);newVersion.chunks[0].version_id='different';await verifyCached(client,newVersion,keyFile,path.join(dir,'version'),cache);assert.equal(calls,3);
  } finally {f.key.fill(0);await fs.rm(dir,{recursive:true,force:true});}
});
test('header/tag comparison ignores ordering and detects meaningful metadata changes',()=>{
  assert(sameHeaders({Metadata:{a:'1',b:'2'},ContentType:'application/octet-stream'},{Metadata:{b:'2',a:'1'},ContentType:'application/octet-stream'}));
  assert(!sameHeaders({ContentEncoding:'gzip'},{ContentEncoding:'identity'}));assert(!sameHeaders({Metadata:{owner:'a'}},{Metadata:{owner:'b'}}));
  assert(sameTags({TagSet:[{Key:'a',Value:'1'},{Key:'b',Value:'2'}]},{TagSet:[{Key:'b',Value:'2'},{Key:'a',Value:'1'}]}));assert(!sameTags({TagSet:[{Key:'a',Value:'1'}]},{TagSet:[{Key:'a',Value:'2'}]}));
});
