import * as fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import * as S3 from '@aws-sdk/client-s3';
import { STSClient, GetCallerIdentityCommand } from '@aws-sdk/client-sts';
import { IAMClient, SimulatePrincipalPolicyCommand } from '@aws-sdk/client-iam';
import { fromIni } from '@aws-sdk/credential-providers';
import { sha, validate, verifyChunk } from './archive.mjs';

export const SOURCE='quantyra-research-archive-485386182336-us-east-1';
export const DEST='quantyra-research-archive-063280428495-us-east-1';
const SOURCE_ACCOUNT='485386182336', DEST_ACCOUNT='063280428495';
const home=os.homedir(), custody=path.join(home,'.quantyra');
export const defaults={catalog:path.join(custody,'archive-catalogs/research-archive-catalog.json'),key:path.join(custody,'credentials/research-archive/surface-migration-20261007.key'),state:path.join(custody,'aws-migration-20261006')};
const check=(ok,m)=>{if(!ok){const e=Error(m);e.safeReason=m.replace(/[^a-zA-Z0-9]+/g,'-').toLowerCase();throw e;}};
const config=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
const send=(client,name,input)=>client.send(new S3[name+'Command'](input));
export async function save(file,value) {
  await fs.mkdir(path.dirname(file),{recursive:true}); const temp=file+'.tmp';
  await fs.writeFile(temp,JSON.stringify(value,null,2)+'\n',{mode:0o600,flag:'wx'}); await fs.rename(temp,file);
}
async function load(file){return JSON.parse(await fs.readFile(file,'utf8'));}
export async function inventory(client,bucket,owner) {
  const rows=[];let KeyMarker,VersionIdMarker;
  for(let page=0;page<100;page++) {
    const r=await send(client,'ListObjectVersions',{Bucket:bucket,ExpectedBucketOwner:owner,MaxKeys:1000,KeyMarker,VersionIdMarker});
    for(const [kind,list] of [['object',r.Versions],['delete-marker',r.DeleteMarkers]]) for(const x of list||[]) rows.push({kind,key:x.Key,version:x.VersionId,bytes:x.Size??0,etag:x.ETag,is_latest:x.IsLatest,last_modified:x.LastModified?.toISOString()});
    if(!r.IsTruncated)return rows;
    check(r.NextKeyMarker && (r.NextKeyMarker!==KeyMarker || r.NextVersionIdMarker!==VersionIdMarker),'Pagination stalled');
    KeyMarker=r.NextKeyMarker;VersionIdMarker=r.NextVersionIdMarker;
  } throw Error('Inventory exceeds bounded 100-page scope');
}
async function identity(profile,account) {
  const r=await new STSClient(config(profile)).send(new GetCallerIdentityCommand({})); check(r.Account===account,'Wrong AWS account');return {account:r.Account,arn:r.Arn};
}
export async function preflight(destination,provision=false) {
  const id=await identity('quantyra',DEST_ACCOUNT);
  // Simulation is a read-only prerequisite; never infer write access from STS.
  const iam=new IAMClient(config('quantyra')), checks=[];
  const bucketActions=['s3:ListBucket','s3:ListBucketVersions','s3:GetBucketVersioning','s3:GetBucketPublicAccessBlock','s3:GetBucketOwnershipControls','s3:GetEncryptionConfiguration'];
  if(provision)bucketActions.push('s3:CreateBucket','s3:PutBucketVersioning','s3:PutBucketPublicAccessBlock','s3:PutBucketOwnershipControls','s3:PutEncryptionConfiguration');
  const objectActions=['s3:GetObjectVersion','s3:PutObject','s3:PutObjectTagging','s3:GetObjectVersionTagging','s3:AbortMultipartUpload','s3:DeleteObject'];
  for(const [actions,resource] of [[bucketActions,`arn:aws:s3:::${DEST}`],[objectActions,`arn:aws:s3:::${DEST}/*`]]) {
    const r=await iam.send(new SimulatePrincipalPolicyCommand({PolicySourceArn:id.arn,ActionNames:actions,ResourceArns:[resource]}));
    check(!r.IsTruncated && r.EvaluationResults?.length===actions.length,'Incomplete permission evaluation');
    for(const e of r.EvaluationResults) {checks.push({action:e.EvalActionName,decision:e.EvalDecision});check(e.EvalDecision==='allowed','Destination permission denied');}
  }
  if(!provision)await controls(destination);
  return {identity:id,checks};
}
async function controls(d) {
  const args={Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT};
  const v=await send(d,'GetBucketVersioning',args),p=await send(d,'GetPublicAccessBlock',args),o=await send(d,'GetBucketOwnershipControls',args),e=await send(d,'GetBucketEncryption',args);
  check(v.Status==='Enabled','Destination versioning required');
  check(['BlockPublicAcls','IgnorePublicAcls','BlockPublicPolicy','RestrictPublicBuckets'].every(k=>p.PublicAccessBlockConfiguration?.[k]===true),'Destination public block required');
  check(o.OwnershipControls?.Rules?.[0]?.ObjectOwnership==='BucketOwnerEnforced','Destination owner enforcement required');
  check(e.ServerSideEncryptionConfiguration?.Rules?.[0]?.ApplyServerSideEncryptionByDefault?.SSEAlgorithm==='AES256','Destination AES256 required');
}
export async function hashBody(body) {const h=createHash('sha256');let bytes=0;for await(const b of body){h.update(b);bytes+=b.length;}return {bytes,sha256:h.digest('hex')};}
// Relay using separate source/destination credentials. No cross-account source
// bucket policy and no disk-sized download. At most one 8 MiB part in memory.
export async function transfer(s,d,row) {
  check(row.kind==='object' && row.bytes<=8*1024**2*10000,'Unsupported object size');
  const src={Bucket:SOURCE,ExpectedBucketOwner:SOURCE_ACCOUNT,Key:row.key,VersionId:row.version};
  const head=await send(s,'HeadObject',src),tags=await send(s,'GetObjectTagging',src);
  check(head.ContentLength===row.bytes && head.ETag===row.etag,'Source changed');
  const args={Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,ServerSideEncryption:'AES256',Metadata:head.Metadata,ContentType:head.ContentType,ContentEncoding:head.ContentEncoding,ContentDisposition:head.ContentDisposition,CacheControl:head.CacheControl,ContentLanguage:head.ContentLanguage,Expires:head.Expires,Tagging:new URLSearchParams((tags.TagSet||[]).map(t=>[t.Key,t.Value])).toString()};
  const body=(await send(s,'GetObject',src)).Body,h=createHash('sha256');let bytes=0,upload,version;
  try {
    if(row.bytes===0) {version=(await send(d,'PutObject',{...args,Body:Buffer.alloc(0),ContentLength:0})).VersionId;body.destroy();}
    else {
      upload=(await send(d,'CreateMultipartUpload',args)).UploadId;check(upload,'Missing upload ID');
      const parts=[];let pending=Buffer.alloc(0);
      const part=async b=>{const PartNumber=parts.length+1; const r=await send(d,'UploadPart',{Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,UploadId:upload,PartNumber,Body:b,ContentLength:b.length});parts.push({PartNumber,ETag:r.ETag});};
      for await(const b of body) {h.update(b);bytes+=b.length;pending=Buffer.concat([pending,b]);while(pending.length>=8*1024**2){await part(pending.subarray(0,8*1024**2));pending=pending.subarray(8*1024**2);}}
      if(pending.length)await part(pending);
      check(bytes===row.bytes,'Source byte count mismatch');
      version=(await send(d,'CompleteMultipartUpload',{Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,UploadId:upload,MultipartUpload:{Parts:parts}})).VersionId;upload=undefined;
    }
    check(version && version!=='null','Destination exact version missing');
    const digest=h.digest('hex'),dst={Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,VersionId:version};
    const verified=await hashBody((await send(d,'GetObject',dst)).Body);
    check(verified.bytes===row.bytes && verified.sha256===digest,'Destination ciphertext mismatch');
    const dh=await send(d,'HeadObject',dst),dt=await send(d,'GetObjectTagging',dst);
    check(JSON.stringify(dh.Metadata||{})===JSON.stringify(head.Metadata||{}) && JSON.stringify(dt.TagSet||[])===JSON.stringify(tags.TagSet||[]),'Metadata/tag mismatch');
    return {...row,destination_version:version,sha256:digest,verified:true};
  } finally { body.destroy(); if(upload)await send(d,'AbortMultipartUpload',{Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,UploadId:upload}); }
}
export function successor(c,mapping,catalogHash) {
  const next=structuredClone(c);next.bucket=DEST;next.profile='quantyra';
  next.migration={source_bucket:SOURCE,source_catalog_sha256:catalogHash,source_profile:c.profile,version_mapping:mapping};
  for(const x of next.chunks){const r=mapping.find(r=>r.kind==='object'&&r.key===x.key&&r.version===x.version_id);check(r?.verified&&r.sha256===x.sha256&&r.bytes===x.bytes,'Catalog version not verified');x.source_version_id=x.version_id;x.version_id=r.destination_version;}
  validate(next);return next;
}
export function successorCompatible(saved,expected,mapping) {
  const withoutMap=c=>{const copy=structuredClone(c);delete copy.migration.version_mapping;return copy;};
  return JSON.stringify(withoutMap(saved))===JSON.stringify(withoutMap(expected)) &&
    saved.migration.version_mapping.every(r=>mapping.some(m=>JSON.stringify(m)===JSON.stringify(r))) &&
    saved.chunks.every(x=>saved.migration.version_mapping.some(r=>r.key===x.key&&r.destination_version===x.version_id&&r.verified));
}
export function orderedRows(rows) {
  const ordered=[...rows].sort((a,b)=>a.key.localeCompare(b.key)||a.last_modified.localeCompare(b.last_modified));
  for(let i=1;i<ordered.length;i++)check(ordered[i-1].key!==ordered[i].key || ordered[i-1].last_modified!==ordered[i].last_modified,'Ambiguous same-time version order');
  return ordered;
}
export async function transferMarker(d,row) {
  check(row.kind==='delete-marker','Expected marker');
  // This command only targets DEST: it recreates historical visibility, never
  // deletes a source version. Root alone owns source retirement.
  const r=await send(d,'DeleteObject',{Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key});
  check(r.DeleteMarker===true&&r.VersionId&&r.VersionId!=='null','Destination marker missing');
  return {...row,destination_version:r.VersionId,verified:true};
}
export async function verifyCatalog(client,c,keyFile,state,restorePath,exactCatalogHash) {
  const {chunks,members}=validate(c),authenticated=new Set(),key=await fs.readFile(keyFile),results=[];
  const selected=restorePath?members.get(restorePath):undefined;
  check(!restorePath || selected && selected.hardlink==null && selected.bytes<=1048576,'Invalid bounded selection');
  await fs.mkdir(state,{recursive:true});const temp=path.join(state,'bounded-restore.pending');
  check(!selected || !(await fs.stat(temp).catch(()=>null)),'Restore staging exists');
  try {
    for(const chunk of [...chunks.values()].sort((a,b)=>a.number-b.number)) {
      const r=await send(client,'GetObject',{Bucket:c.bucket,ExpectedBucketOwner:c.bucket===SOURCE?SOURCE_ACCOUNT:DEST_ACCOUNT,Key:chunk.key,VersionId:chunk.version_id});
      const result={...await verifyChunk(r.Body,chunk,members,key,authenticated,selected?.chunk===chunk.number?{...selected,temp}:undefined),key:chunk.key,version_id:chunk.version_id};results.push(result);
      await save(path.join(state,'verification-progress.json'),{catalog_canonical_sha256:sha(Buffer.from(JSON.stringify(c))),catalog_sha256:exactCatalogHash,completed:results,complete:false});
      console.log(JSON.stringify({chunk:chunk.number,authenticated_members:result.members,status:'verified'}));
    }
    check(authenticated.size===members.size,'Incomplete member verification');
    let restored;
    if(selected){const r=await hashBody((await import('node:fs')).createReadStream(temp));check(r.bytes===selected.bytes&&r.sha256===selected.sha256,'Restore hash mismatch');const output=path.join(state,'bounded-restore.verified');await fs.copyFile(temp,output,(await import('node:fs')).constants.COPYFILE_EXCL);await fs.rm(temp);restored={bytes:r.bytes,sha256:r.sha256,output};}
    const receipt={bucket:c.bucket,catalog_canonical_sha256:sha(Buffer.from(JSON.stringify(c))),catalog_sha256:exactCatalogHash,chunks:results,members:authenticated.size,complete:true,restored};await save(path.join(state,'verification.json'),receipt);return receipt;
  } finally {key.fill(0);await fs.rm(temp,{force:true});}
}
async function main() {
  const mode=process.argv[2];check(['discover','preflight','provision','copy','copy-core','verify-source','verify-destination','activate'].includes(mode),'Unknown mode');
  const s=new S3.S3Client(config('cyint-ea-prod')),d=new S3.S3Client(config('quantyra'));
  await identity('cyint-ea-prod',SOURCE_ACCOUNT);await identity('quantyra',DEST_ACCOUNT);
  const catalogBytes=await fs.readFile(defaults.catalog),c=JSON.parse(catalogBytes);check(c.bucket===SOURCE,'Historical catalog source mismatch');validate(c);
  if(mode==='discover') {
    const rows=await inventory(s,SOURCE,SOURCE_ACCOUNT);await save(path.join(defaults.state,'source-versions.json'),{bucket:SOURCE,catalog_sha256:sha(catalogBytes),rows});
    const summary={at:new Date().toISOString(),objects:rows.filter(x=>x.kind==='object').length,delete_markers:rows.filter(x=>x.kind==='delete-marker').length,bytes:rows.reduce((n,x)=>n+x.bytes,0),catalog_chunks:c.chunks.length,catalog_members:c.members.length,catalog_sha256:sha(catalogBytes)};
    for(const x of c.chunks)check(rows.some(r=>r.key===x.key&&r.version===x.version_id&&r.bytes===x.bytes),'Catalog source version missing');
    await save(path.join(defaults.state,'discovery-summary.json'),summary);console.log(JSON.stringify(summary));return;
  }
  if(mode==='verify-source'||mode==='verify-destination') {
    const cat=mode==='verify-source'?c:await load(path.join(defaults.state,'successor-catalog.json'));
    const selected=cat.members.filter(m=>m.hardlink==null&&m.path.startsWith('realizable-cmmsa-hardness/')&&/\.log$/.test(m.path)&&m.bytes>0&&m.bytes<=65536).sort((a,b)=>a.bytes-b.bytes)[0];
    const exact=mode==='verify-source'?sha(catalogBytes):sha(await fs.readFile(path.join(defaults.state,'successor-catalog.json')));
    check(selected,'No bounded log selection');const receipt=await verifyCatalog(mode==='verify-source'?s:d,cat,defaults.key,path.join(defaults.state,mode),selected.path,exact);
    console.log(JSON.stringify({complete:receipt.complete,chunks:receipt.chunks.length,members:receipt.members,restore_bytes:receipt.restored.bytes,restore_sha256:receipt.restored.sha256}));return;
  }
  const gate=await preflight(d,mode==='provision');await save(path.join(defaults.state,'destination-preflight.json'),{at:new Date().toISOString(),...gate});
  if(mode==='preflight'){console.log('Destination permissions and controls verified');return;}
  if(mode==='provision') {
    // Existing buckets are never reconfigured by this creation mode.
    const buckets=await send(d,'ListBuckets',{});check(!buckets.Buckets?.some(b=>b.Name===DEST),'Destination exists; inspect controls before copy');
    await send(d,'CreateBucket',{Bucket:DEST,ObjectOwnership:'BucketOwnerEnforced'});
    const a={Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT};
    await send(d,'PutPublicAccessBlock',{...a,PublicAccessBlockConfiguration:{BlockPublicAcls:true,IgnorePublicAcls:true,BlockPublicPolicy:true,RestrictPublicBuckets:true}});
    await send(d,'PutBucketVersioning',{...a,VersioningConfiguration:{Status:'Enabled'}});
    await send(d,'PutBucketEncryption',{...a,ServerSideEncryptionConfiguration:{Rules:[{ApplyServerSideEncryptionByDefault:{SSEAlgorithm:'AES256'}}]}});await controls(d);return;
  }
  const snapshot=await load(path.join(defaults.state,'source-versions.json'));check(snapshot.catalog_sha256===sha(catalogBytes),'Catalog changed');
  const live=await inventory(s,SOURCE,SOURCE_ACCOUNT),core=r=>r.key.startsWith('migrations/surface-migration-20261007/');
  const rows=mode==='copy-core'?live.filter(core):live,expected=mode==='copy-core'?snapshot.rows.filter(core):snapshot.rows;
  check(JSON.stringify(rows)===JSON.stringify(expected),'Source inventory changed');
  const mapFile=path.join(defaults.state,'version-mapping.json');const mapping=await load(mapFile).catch(e=>{if(e.code==='ENOENT')return [];throw e;});
  if(mode==='copy'||mode==='copy-core') {
    for(const row of orderedRows(rows)) {
      const existing=mapping.find(x=>x.key===row.key&&x.version===row.version);
      if(existing){if(row.kind==='object'){const r=await hashBody((await send(d,'GetObject',{Bucket:DEST,ExpectedBucketOwner:DEST_ACCOUNT,Key:row.key,VersionId:existing.destination_version})).Body);check(r.sha256===existing.sha256&&r.bytes===row.bytes,'Resume verification failed');}continue;}
      mapping.push(row.kind==='object'?await transfer(s,d,row):await transferMarker(d,row));await save(mapFile,mapping);console.log(JSON.stringify({copied_versions:mapping.length,total:rows.length}));
    }
    check(rows.every(r=>mapping.some(m=>m.key===r.key&&m.version===r.version&&m.verified)),'Incomplete mapping');
    const destination=await inventory(d,DEST,DEST_ACCOUNT);
    for(const row of rows){const m=mapping.find(m=>m.key===row.key&&m.version===row.version);check(destination.some(x=>x.key===row.key&&x.version===m.destination_version&&x.kind===row.kind),'Destination inventory mismatch');if(row.is_latest)check(destination.some(x=>x.key===row.key&&x.version===m.destination_version&&x.is_latest),'Destination visibility differs');}
    await save(path.join(defaults.state,'successor-catalog.json'),successor(c,mapping,sha(catalogBytes)));return;
  }
  if(mode==='activate') {
    const receipt=await load(path.join(defaults.state,'verify-destination/verification.json'));check(receipt.complete&&receipt.members===c.members.length&&receipt.chunks.length===c.chunks.length,'Destination not authenticated');
    const next=await load(path.join(defaults.state,'successor-catalog.json'));check(successorCompatible(next,successor(c,mapping,sha(catalogBytes)),mapping),'Successor changed');
    check(receipt.catalog_canonical_sha256===sha(Buffer.from(JSON.stringify(next)))&&next.chunks.every(x=>receipt.chunks.some(r=>r.number===x.number&&r.version_id===x.version_id&&r.ciphertext_sha256===x.sha256&&r.tar_sha256===x.tar_sha256)),'Authentication receipt version mismatch');
    // Write a separate active successor; historical catalog is immutable.
    await save(path.join(custody,'archive-catalogs/research-archive-catalog.quantyra.json'),next);console.log('Successor catalog activated at separate Quantyra path');
  }
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) main().catch(async e=>{
  const failure={at:new Date().toISOString(),mode:process.argv[2],error:/^[A-Za-z][A-Za-z0-9]+$/.test(e.name)?e.name:'Error',safe_reason:e.safeReason??null,http_status:e.$metadata?.httpStatusCode??null,status:'blocked-or-failed'};
  // Never print AWS response bodies, SDK error messages, headers or payloads.
  await save(path.join(defaults.state,process.argv[2]+'-failure.json'),failure).catch(()=>{});console.error(JSON.stringify(failure));process.exitCode=1;
});
