// Core copy and destination authentication share one streamed destination read.
// Previously authenticated source receipts bind the expected ciphertext hash.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import { SOURCE,DEST,defaults,preflight,inventory,hashBody,save,successor,orderedRows } from './migrate.mjs';
import { validate,sha,verifyChunk } from './archive.mjs';
import { samePolicy } from './policy.mjs';
const cfg=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
const s=new S3.S3Client(cfg('cyint-ea-prod')),d=new S3.S3Client(cfg('quantyra'));
const send=(c,n,a)=>c.send(new S3[n+'Command'](a)),read=p=>fs.readFile(p,'utf8').then(JSON.parse);
const check=(ok,reason)=>{if(!ok){const e=Error();e.safeReason=reason;throw e;}};
const dest={Bucket:DEST,ExpectedBucketOwner:'063280428495'},state=defaults.state,lock=path.join(state,'copy-core.lock');
async function main() {
  check(false,'legacy-core-actor-disabled-use-repair-copy-at-safe-boundary');
  await preflight(d);
  const policy=await read(path.join(state,'temporary-copy-policy.json')),installed=await send(d,'GetBucketPolicy',dest);check(samePolicy(policy,JSON.parse(installed.Policy)),'copy-bridge-mismatch');
  const bytes=await fs.readFile(defaults.catalog),c=JSON.parse(bytes),{chunks,members}=validate(c),catalogHash=sha(bytes);
  const snapshot=await read(path.join(state,'source-versions.json'));check(snapshot.catalog_sha256===catalogHash,'historical-catalog-changed');
  const core=r=>r.key.startsWith('migrations/surface-migration-20261007/'),live=(await inventory(s,SOURCE,'485386182336')).filter(core),rows=snapshot.rows.filter(core);
  check(JSON.stringify(live)===JSON.stringify(rows),'core-source-inventory-changed');check(rows.every(r=>r.kind==='object'&&r.bytes<=5*1024**3),'unsupported-core-event');
  const pending=await send(d,'ListMultipartUploads',dest);check(!(pending.Uploads||[]).length,'relay-still-active');
  const lockHandle=await fs.open(lock,'wx',0o600);await lockHandle.writeFile(JSON.stringify({pid:process.pid,at:new Date().toISOString()}));await lockHandle.close();
  let key;const verification=path.join(state,'verify-destination'),temp=path.join(verification,'copy-bounded.pending');
  try {
    key=await fs.readFile(defaults.key);const authenticated=new Set(),results=[],mapFile=path.join(state,'version-mapping.json');
    const mapping=await read(mapFile).catch(e=>{if(e.code==='ENOENT')return [];throw e;});
    await fs.mkdir(verification,{recursive:true});check(!(await fs.stat(temp).catch(()=>null)),'restore-staging-exists');
    const selected=c.members.filter(m=>m.hardlink==null&&m.path.startsWith('realizable-cmmsa-hardness/')&&/\.log$/.test(m.path)&&m.bytes>0&&m.bytes<=65536).sort((a,b)=>a.bytes-b.bytes)[0];check(selected,'no-bounded-log');
    const destinationInventory=await inventory(d,DEST,'063280428495');
    for(const row of orderedRows(rows)) {
      const chunk=[...chunks.values()].find(x=>x.key===row.key&&x.version_id===row.version),prior=mapping.find(x=>x.key===row.key&&x.version===row.version);
      let version=prior?.destination_version,method=prior?.copy_method??'server-side';
      if(!version) {
        const orphan=destinationInventory.filter(x=>x.key===row.key&&x.kind==='object'&&!mapping.some(m=>m.destination_version===x.version&&m.key===x.key));
        check(orphan.length<=1,'ambiguous-unmapped-destination-versions');
        if(orphan.length){version=orphan[0].version;method='recovered-interrupted-server-copy';}
        else {const r=await send(s,'CopyObject',{...dest,Key:row.key,CopySource:SOURCE+'/'+row.key.split('/').map(encodeURIComponent).join('/')+'?versionId='+encodeURIComponent(row.version),CopySourceIfMatch:row.etag,ExpectedSourceBucketOwner:'485386182336',ServerSideEncryption:'AES256',MetadataDirective:'COPY',TaggingDirective:'COPY'});version=r.VersionId;}
      }
      check(version&&version!=='null','destination-exact-version-missing');
      const target={...dest,Key:row.key,VersionId:version};let digest;
      if(chunk) {
        const proof=await read(path.join(state,'verify-source/verification-progress.json'));
        check((proof.catalog_canonical_sha256??proof.catalog_sha256)===sha(Buffer.from(JSON.stringify(c)))&&proof.completed.some(x=>x.number===chunk.number&&x.authenticated&&x.ciphertext_sha256===chunk.sha256&&x.tar_sha256===chunk.tar_sha256),'source-chunk-authentication-pending');
        const r=await verifyChunk((await send(d,'GetObject',target)).Body,chunk,members,key,authenticated,selected.chunk===chunk.number?{...selected,temp}:undefined);
        results.push({...r,key:row.key,version_id:version});digest={bytes:r.bytes,sha256:r.ciphertext_sha256};
        await save(path.join(verification,'verification-progress.json'),{catalog_source_sha256:catalogHash,completed:results,complete:false});
      } else {
        const src=await hashBody((await send(s,'GetObject',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version})).Body);
        digest=await hashBody((await send(d,'GetObject',target)).Body);check(digest.bytes===src.bytes&&digest.sha256===src.sha256,'opaque-object-hash-mismatch');
      }
      check(digest.bytes===row.bytes&&(!prior||prior.sha256===digest.sha256),'version-hash-mismatch');
      const meta=await Promise.allSettled([send(s,'HeadObject',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version}),send(d,'HeadObject',target),send(s,'GetObjectTagging',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version}),send(d,'GetObjectTagging',target)]);
      for(const r of meta)if(r.status==='rejected')throw r.reason;
      const [sh,dh,st,dt]=meta.map(r=>r.value);check(sh.ETag===row.etag&&JSON.stringify(sh.Metadata||{})===JSON.stringify(dh.Metadata||{})&&JSON.stringify(st.TagSet||[])===JSON.stringify(dt.TagSet||[]),'metadata-or-tag-mismatch');
      if(!prior){mapping.push({...row,destination_version:version,sha256:digest.sha256,verified:true,copy_method:method});await save(mapFile,mapping);}
      console.log(JSON.stringify({mapped_core_versions:rows.filter(x=>mapping.some(m=>m.key===x.key&&m.version===x.version)).length,authenticated_chunks:results.length,authenticated_members:authenticated.size}));
    }
    check(results.length===c.chunks.length&&authenticated.size===members.size,'core-authentication-incomplete');
    const after=(await inventory(s,SOURCE,'485386182336')).filter(core),destRows=await inventory(d,DEST,'063280428495');check(JSON.stringify(after)===JSON.stringify(rows),'source-changed-during-copy');
    for(const row of rows){const m=mapping.find(x=>x.key===row.key&&x.version===row.version);check(m?.verified&&destRows.some(x=>x.key===row.key&&x.version===m.destination_version&&(!row.is_latest||x.is_latest)),'core-version-visibility-mismatch');}
    const next=successor(c,mapping,catalogHash);await save(path.join(state,'successor-catalog.json'),next);
    const restored=await hashBody((await import('node:fs')).createReadStream(temp));check(restored.bytes===selected.bytes&&restored.sha256===selected.sha256,'bounded-restore-mismatch');
    const output=path.join(verification,'copy-bounded.verified');await fs.copyFile(temp,output,(await import('node:fs')).constants.COPYFILE_EXCL);
    await save(path.join(verification,'verification.json'),{bucket:DEST,catalog_canonical_sha256:sha(Buffer.from(JSON.stringify(next))),catalog_sha256:sha(await fs.readFile(path.join(state,'successor-catalog.json'))),chunks:results,members:authenticated.size,complete:true,restored:{...restored,output}});
    await save(path.join(state,'copy-core-receipt.json'),{at:new Date().toISOString(),scope:'surface-migration-prefix',versions:rows.length,bytes:rows.reduce((n,r)=>n+r.bytes,0),complete:true});
  } finally {key?.fill(0);await fs.rm(temp,{force:true});await fs.rm(lock);}
}
main().catch(async e=>{const r={at:new Date().toISOString(),error:e.name,safe_reason:e.safeReason??null,http_status:e.$metadata?.httpStatusCode??null};await save(path.join(state,'copy-authenticate-core-failure.json'),r).catch(()=>{});console.error(JSON.stringify(r));process.exitCode=1;});
