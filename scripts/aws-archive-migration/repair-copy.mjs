// Single writer, interruption-safe resumption at a verified process boundary.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import {fromIni} from '@aws-sdk/credential-providers';
import {SOURCE,DEST,defaults,inventory,save,hashBody,preflight,orderedRows,successor} from './migrate.mjs';
import {sha,validate,verifyChunk} from './archive.mjs';
import {sameHeaders,sameTags} from './verify-version-mapping.mjs';
import {samePolicy} from './policy.mjs';
import {digest,identity,requireThat as check,uniqueInventory,mappingCoverage,reconcileVersion,stableInventories,orderCandidates} from './custody.mjs';
const cfg=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
const s=new S3.S3Client(cfg('cyint-ea-prod')),d=new S3.S3Client(cfg('quantyra'));
const send=(c,n,a)=>c.send(new S3[n+'Command'](a)),read=p=>fs.readFile(p,'utf8').then(JSON.parse),state=defaults.state,base=path.join(state,'repair');
const src=r=>({Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:r.key,VersionId:r.version}),dst=(r,v)=>({Bucket:DEST,ExpectedBucketOwner:'063280428495',Key:r.key,VersionId:v});
async function main(){
  // A stale original lock is evidence, not permission to overlap a live actor.
  const old=await read(path.join(state,'copy-core.lock')).catch(e=>{if(e.code==='ENOENT')return null;throw e;});
  if(old){let alive=false;try{process.kill(old.pid,0);alive=true;}catch(e){check(e.code==='ESRCH','cannot-check-old-actor');}check(!alive,'original-actor-still-alive');}
  await fs.mkdir(base,{recursive:true});const lock=path.join(base,'writer.lock'),handle=await fs.open(lock,'wx',0o600);await handle.writeFile(JSON.stringify({pid:process.pid,at:new Date().toISOString()}));await handle.close();
  let key;
  try{
    await preflight(d);const policy=await read(path.join(state,'temporary-copy-policy.json'));check(samePolicy(policy,JSON.parse((await send(d,'GetBucketPolicy',{Bucket:DEST,ExpectedBucketOwner:'063280428495'})).Policy)),'bridge-not-verified');
    const snapshot=await read(path.join(state,'source-versions.json')),start=await inventory(s,SOURCE,'485386182336');uniqueInventory(start);check(digest(start)===digest(snapshot.rows)&&start.length===205,'source-snapshot-mismatch');
    const sourceBytes=await fs.readFile(defaults.catalog),c=JSON.parse(sourceBytes),{chunks,members}=validate(c);check(sha(sourceBytes)===snapshot.catalog_sha256,'source-catalog-changed');
    key=await fs.readFile(defaults.key);const mapping=await read(path.join(state,'version-mapping.json')),completed=await read(path.join(base,'core-progress.json')).catch(e=>{if(e.code==='ENOENT')return read(path.join(state,'verify-destination/verification-progress.json'));throw e;});
    check(completed.catalog_source_sha256===sha(sourceBytes),'old-proof-catalog-mismatch');const results=completed.completed,reusedCount=results.length,authenticated=new Set();
    for(const r of results){const x=chunks.get(r.number),m=mapping.find(y=>y.key===r.key&&y.destination_version===r.version_id);check(x&&r.authenticated&&r.key===x.key&&r.bytes===x.bytes&&r.ciphertext_sha256===x.sha256&&r.tar_sha256===x.tar_sha256&&(!m||m.verified&&m.sha256===x.sha256),'old-proof-identity-mismatch');for(const y of members.values())if(y.chunk===r.number)authenticated.add(y.path);}
    const initialDest=await inventory(d,DEST,'063280428495');uniqueInventory(initialDest);
    const preserved=path.join(base,'initial-mapping.'+digest(mapping)+'.json');await fs.writeFile(preserved,JSON.stringify(mapping,null,2)+'\n',{flag:'wx',mode:0o600}).catch(e=>{if(e.code!=='EEXIST')throw e;});
    const code={};for(const f of ['repair-copy.mjs','custody.mjs','archive.mjs','migrate.mjs','verify-version-mapping.mjs']){const bytes=await fs.readFile(new URL(f,import.meta.url));code[f]=sha(bytes);const dir=path.join(base,'runtime-source',code[f]);await fs.mkdir(dir,{recursive:true});await fs.writeFile(path.join(dir,f),bytes,{flag:'wx',mode:0o600}).catch(e=>{if(e.code!=='EEXIST')throw e;});check(sha(await fs.readFile(path.join(dir,f)))===code[f],'runtime-source-custody-mismatch');}const previousCode=await fs.readFile(path.join(base,'runtime-code.json')).catch(e=>{if(e.code==='ENOENT')return null;throw e;});if(previousCode)await fs.writeFile(path.join(base,'runtime-code.'+sha(previousCode)+'.json'),previousCode,{flag:'wx',mode:0o600}).catch(e=>{if(e.code!=='EEXIST')throw e;});await save(path.join(base,'runtime-code.json'),code);
    const hashCache=new Map(mapping.map(m=>[identity(m),{bytes:m.bytes,sha256:m.sha256}]));
    async function verify(row,version,chunk){
      const [sh,dh,st,dt]=await Promise.all([send(s,'HeadObject',src(row)),send(d,'HeadObject',dst(row,version)),send(s,'GetObjectTagging',src(row)),send(d,'GetObjectTagging',dst(row,version))]);
      if(sh.ETag!==row.etag||sh.ContentLength!==row.bytes||dh.ContentLength!==row.bytes||dh.ServerSideEncryption!=='AES256'||!sameHeaders(sh,dh)||!sameTags(st,dt))return null;
      let proof;if(chunk){const prior=results.find(x=>x.key===row.key&&x.version_id===version);const r=prior??await verifyChunk((await send(d,'GetObject',dst(row,version))).Body,chunk,members,key,authenticated);proof={bytes:r.bytes,sha256:r.ciphertext_sha256};if(!prior){results.push({...r,key:row.key,version_id:version});await save(path.join(base,'core-progress.json'),{catalog_source_sha256:sha(sourceBytes),completed:results,complete:false});}}
      else{let expected=hashCache.get(identity(row));if(!expected){expected=await hashBody((await send(s,'GetObject',src(row))).Body);hashCache.set(identity(row),expected);}proof=await hashBody((await send(d,'GetObject',dst(row,version))).Body);if(proof.sha256!==expected.sha256||proof.bytes!==expected.bytes)return null;}
      check(proof.bytes===row.bytes&&(!chunk||proof.sha256===chunk.sha256),'byte-hash-mismatch');return proof;
    }
    for(const row of orderedRows(start)){
      if(mapping.some(m=>identity(m)===identity(row)))continue;
      const available=orderCandidates(row,(await inventory(d,DEST,'063280428495')).filter(x=>x.key===row.key&&x.kind===row.kind&&!mapping.some(m=>m.key===x.key&&m.destination_version===x.version)));
      const journal=path.join(base,'copy-journal',digest([row.key,row.version])+'.json'),chunk=[...chunks.values()].find(x=>x.key===row.key&&x.version_id===row.version);
      const r=await reconcileVersion({row,candidates:available,verify:v=>verify(row,v,chunk),intent:()=>save(journal,{source:row,phase:'intent',at:new Date().toISOString()}),result:v=>save(journal,{source:row,destination_version:v,phase:'reply',at:new Date().toISOString()}),copy:async()=>{const r=await send(s,'CopyObject',{Bucket:DEST,ExpectedBucketOwner:'063280428495',Key:row.key,CopySource:SOURCE+'/'+row.key.split('/').map(encodeURIComponent).join('/')+'?versionId='+encodeURIComponent(row.version),CopySourceIfMatch:row.etag,ExpectedSourceBucketOwner:'485386182336',ServerSideEncryption:'AES256',MetadataDirective:'COPY',TaggingDirective:'COPY'});return r.VersionId;}});
      mapping.push({...row,destination_version:r.version,sha256:r.proof.sha256,verified:true,copy_method:r.reconciled?'reconciled-interrupted-copy':'journaled-server-copy'});await save(path.join(state,'version-mapping.json'),mapping);await save(journal,{source:row,destination_version:r.version,phase:'verified-mapped',sha256:r.proof.sha256,reconciled:r.reconciled,at:new Date().toISOString()});console.log(JSON.stringify({mapped_versions:mapping.length,total:205,core_authenticated:results.length}));
    }
    const destination=await inventory(d,DEST,'063280428495'),retained=[];
    for(const x of destination.filter(x=>!mapping.some(m=>m.key===x.key&&m.destination_version===x.version))){const m=mapping.find(m=>m.key===x.key&&m.bytes===x.bytes);check(m,'foreign-destination-version');const proof=await verify(m,x.version);check(proof&&proof.sha256===m.sha256,'retained-duplicate-hash-mismatch');retained.push({...x,source_identity:identity(m),reason:'interrupted-copy-duplicate',retained:true,verified:true,sha256:proof.sha256});}
    mappingCoverage(start,mapping,destination,retained);const end=await inventory(s,SOURCE,'485386182336'),destEnd=await inventory(d,DEST,'063280428495');stableInventories(start,end,destination,destEnd);
    await save(path.join(base,'retained-versions.json'),retained);await save(path.join(base,'destination-versions.json'),destination);
    check(results.length===51&&authenticated.size===members.size,'core-authentication-incomplete');const next=successor(c,mapping,sha(sourceBytes)),nextFile=path.join(base,'core-successor.json');await save(nextFile,next);
    await save(path.join(base,'core-authentication.json'),{bucket:DEST,catalog_sha256:sha(await fs.readFile(nextFile)),catalog_canonical_sha256:digest(next),member_catalog_sha256:digest(next.members),members:members.size,chunks:results,complete:true,reused_immutable_chunks:reusedCount});
    await save(path.join(base,'copy-all-receipt.json'),{type:'archive-author-copy-v1',at:new Date().toISOString(),complete:true,versions:start.length,bytes:start.reduce((n,x)=>n+x.bytes,0),source_inventory_sha256:sha(await fs.readFile(path.join(state,'source-versions.json'))),source_rows_sha256:digest(start),mapping_sha256:sha(await fs.readFile(path.join(state,'version-mapping.json'))),destination_inventory_sha256:sha(await fs.readFile(path.join(base,'destination-versions.json'))),retained_versions_sha256:sha(await fs.readFile(path.join(base,'retained-versions.json'))),source_stable:true,destination_stable:true,code});
  }finally{key?.fill(0);await fs.rm(lock);}
}
main().catch(async e=>{const r={at:new Date().toISOString(),status:'repair-copy-failed',error:e.name,safe_reason:e.safeReason??null,http_status:e.$metadata?.httpStatusCode??null};await save(path.join(base,'failure.json'),r).catch(()=>{});console.error(JSON.stringify(r));process.exitCode=1;});
