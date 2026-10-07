// Optional server-side copy avoids relaying gigabytes through the workstation.
// The destination-only bridge grants one named source user copy-only access,
// expires automatically, and is removed after verified migration.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import { STSClient, GetCallerIdentityCommand } from '@aws-sdk/client-sts';
import { IAMClient, SimulatePrincipalPolicyCommand } from '@aws-sdk/client-iam';
import { fromIni } from '@aws-sdk/credential-providers';
import { SOURCE, DEST, defaults, preflight, inventory, hashBody, save, successor, successorCompatible, orderedRows } from './migrate.mjs';
import { sha } from './archive.mjs';
import { samePolicy } from './policy.mjs';
const cfg=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
const s=new S3.S3Client(cfg('cyint-ea-prod')),d=new S3.S3Client(cfg('quantyra'));
const check=(ok,reason)=>{if(!ok){const e=Error();e.safeReason=reason;throw e;}};
const send=(c,n,a)=>c.send(new S3[n+'Command'](a));
const destArgs={Bucket:DEST,ExpectedBucketOwner:'063280428495'};
const read=file=>fs.readFile(file,'utf8').then(JSON.parse);
const policyFile=path.join(defaults.state,'temporary-copy-policy.json');
async function policyPermissions() {
  const r=await new IAMClient(cfg('quantyra')).send(new SimulatePrincipalPolicyCommand({PolicySourceArn:'arn:aws:iam::063280428495:user/ServiceAdmin',ActionNames:['s3:GetBucketPolicy','s3:PutBucketPolicy','s3:DeleteBucketPolicy'],ResourceArns:[`arn:aws:s3:::${DEST}`]}));
  check(r.EvaluationResults?.length===3&&r.EvaluationResults.every(x=>x.EvalDecision==='allowed'),'bucket-policy-permission-denied');
}
async function bridge() {
  await preflight(d);await policyPermissions();
  const id=await new STSClient(cfg('cyint-ea-prod')).send(new GetCallerIdentityCommand({}));check(id.Account==='485386182336'&&id.Arn==='arn:aws:iam::485386182336:user/cyint-ea','unexpected-source-principal');
  const policy={Version:'2012-10-17',Statement:[{Sid:'QuantyraTemporaryVersionCopy20261006',Effect:'Allow',Principal:{AWS:id.Arn},Action:['s3:PutObject','s3:PutObjectTagging'],Resource:`arn:aws:s3:::${DEST}/migrations/*`,Condition:{Bool:{'aws:SecureTransport':'true'},DateLessThan:{'aws:CurrentTime':'2026-10-08T12:00:00Z'},StringLike:{'s3:x-amz-copy-source':`${SOURCE}/migrations/*`},StringEquals:{'s3:x-amz-server-side-encryption':'AES256'}}}]};
  policy.Statement[0].Action=['s3:PutObject'];
  policy.Statement.push({Sid:'QuantyraTemporaryCopyTags20261006',Effect:'Allow',Principal:{AWS:id.Arn},Action:['s3:PutObjectTagging'],Resource:`arn:aws:s3:::${DEST}/migrations/*`,Condition:{Bool:{'aws:SecureTransport':'true'},DateLessThan:{'aws:CurrentTime':'2026-10-08T12:00:00Z'}}});
  const simulation=await new IAMClient(cfg('cyint-ea-prod')).send(new SimulatePrincipalPolicyCommand({PolicySourceArn:id.Arn,CallerArn:id.Arn,ResourceOwner:'arn:aws:iam::063280428495:root',ResourcePolicy:JSON.stringify(policy),ActionNames:['s3:PutObject','s3:PutObjectTagging'],ResourceArns:[`arn:aws:s3:::${DEST}/migrations/surface-migration-20261007/archive-0001.qarc`],ContextEntries:[{ContextKeyName:'aws:SecureTransport',ContextKeyType:'boolean',ContextKeyValues:['true']},{ContextKeyName:'aws:CurrentTime',ContextKeyType:'date',ContextKeyValues:[new Date().toISOString()]},{ContextKeyName:'s3:x-amz-copy-source',ContextKeyType:'string',ContextKeyValues:[`${SOURCE}/migrations/surface-migration-20261007/archive-0001.qarc?versionId=fixture`]},{ContextKeyName:'s3:x-amz-server-side-encryption',ContextKeyType:'string',ContextKeyValues:['AES256']}]}));
  const decisions=simulation.EvaluationResults?.map(x=>({action:x.EvalActionName,decision:x.EvalDecision,policy_types:x.EvalDecisionDetails,missing_context:x.MissingContextValues}));
  await save(path.join(defaults.state,'server-copy-simulation.json'),{at:new Date().toISOString(),decisions});
  if(!simulation.EvaluationResults?.length || simulation.EvaluationResults.some(x=>x.EvalDecision!=='allowed'))console.log(JSON.stringify({decisions}));
  check(simulation.EvaluationResults?.length===2&&simulation.EvaluationResults.every(x=>x.EvalDecision==='allowed'),'cross-account-copy-permission-denied');
  const existing=await send(d,'GetBucketPolicy',destArgs).catch(e=>{if(e.name==='NoSuchBucketPolicy')return null;throw e;});
  check(!existing || samePolicy(JSON.parse(existing.Policy),policy),'unrelated-destination-policy');
  await save(policyFile,policy);await save(path.join(defaults.state,'server-copy-permissions.json'),{at:new Date().toISOString(),source_principal:id.Arn,checks:simulation.EvaluationResults.map(x=>({action:x.EvalActionName,decision:x.EvalDecision})),expires:'2026-10-08T12:00:00Z'});
  if(!existing)await send(d,'PutBucketPolicy',{...destArgs,Policy:JSON.stringify(policy)});
  const installed=await send(d,'GetBucketPolicy',destArgs);check(samePolicy(JSON.parse(installed.Policy),policy),'bridge-readback-mismatch');console.log('Copy-only destination bridge verified');
}
async function cancelRelay() {
  await preflight(d);const r=await send(d,'ListMultipartUploads',{...destArgs,Prefix:'migrations/surface-migration-20261007/'});
  check(!r.IsTruncated&&(r.Uploads||[]).length<=1,'ambiguous-upload-cancellation');
  for(const u of r.Uploads||[]){await send(d,'AbortMultipartUpload',{...destArgs,Key:u.Key,UploadId:u.UploadId});}
  console.log(JSON.stringify({aborted_incomplete_destination_uploads:(r.Uploads||[]).length}));
}
async function copy(core) {
  await preflight(d);const installed=await send(d,'GetBucketPolicy',destArgs),policy=await read(policyFile);check(samePolicy(JSON.parse(installed.Policy),policy),'bridge-not-verified');
  const snapshot=await read(path.join(defaults.state,'source-versions.json')),live=await inventory(s,SOURCE,'485386182336'),filter=r=>!core||r.key.startsWith('migrations/surface-migration-20261007/');
  const rows=live.filter(filter);check(JSON.stringify(rows)===JSON.stringify(snapshot.rows.filter(filter)),'source-inventory-changed');check(!rows.some(r=>r.kind!=='object'||r.bytes>5*1024**3),'relay-required-for-large-object-or-marker');
  const mapFile=path.join(defaults.state,'version-mapping.json'),mapping=await read(mapFile).catch(e=>{if(e.code==='ENOENT')return [];throw e;});
  const uploads=await send(d,'ListMultipartUploads',destArgs);check(!(uploads.Uploads||[]).length,'relay-still-active');
  for(const row of orderedRows(rows)) {
    const prior=mapping.find(m=>m.key===row.key&&m.version===row.version);if(prior)continue;
    const copied=await send(s,'CopyObject',{...destArgs,Key:row.key,CopySource:SOURCE+'/'+row.key.split('/').map(encodeURIComponent).join('/')+'?versionId='+encodeURIComponent(row.version),CopySourceIfMatch:row.etag,ExpectedSourceBucketOwner:'485386182336',ServerSideEncryption:'AES256',MetadataDirective:'COPY',TaggingDirective:'COPY'});
    check(copied.VersionId&&copied.VersionId!=='null','destination-version-missing');
    const pair=await Promise.allSettled([
      (async()=>hashBody((await send(s,'GetObject',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version})).Body))(),
      (async()=>hashBody((await send(d,'GetObject',{...destArgs,Key:row.key,VersionId:copied.VersionId})).Body))()
    ]);
    for(const r of pair)if(r.status==='rejected')throw r.reason;
    const [src,dst]=pair.map(r=>r.value);
    check(src.bytes===row.bytes&&dst.bytes===row.bytes&&src.sha256===dst.sha256,'ciphertext-verification-failed');
    const metadata=await Promise.allSettled([
      send(s,'HeadObject',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version}),
      send(d,'HeadObject',{...destArgs,Key:row.key,VersionId:copied.VersionId}),
      send(s,'GetObjectTagging',{Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version}),
      send(d,'GetObjectTagging',{...destArgs,Key:row.key,VersionId:copied.VersionId})
    ]);
    for(const r of metadata)if(r.status==='rejected')throw r.reason;
    const [sh,dh,st,dt]=metadata.map(r=>r.value);
    check(JSON.stringify(sh.Metadata||{})===JSON.stringify(dh.Metadata||{})&&JSON.stringify(st.TagSet||[])===JSON.stringify(dt.TagSet||[]),'metadata-tag-verification-failed');
    mapping.push({...row,destination_version:copied.VersionId,sha256:dst.sha256,verified:true,copy_method:'server-side'});await save(mapFile,mapping);console.log(JSON.stringify({copied_versions:mapping.length,scope_versions:rows.length}));
  }
  const catalogBytes=await fs.readFile(defaults.catalog),catalog=JSON.parse(catalogBytes);check(snapshot.catalog_sha256===sha(catalogBytes),'historical-catalog-changed');
  const after=(await inventory(s,SOURCE,'485386182336')).filter(filter),destination=await inventory(d,DEST,'063280428495');
  check(JSON.stringify(after)===JSON.stringify(rows),'source-changed-during-copy');
  for(const row of rows){const m=mapping.find(x=>x.key===row.key&&x.version===row.version);check(m?.verified&&destination.some(x=>x.key===row.key&&x.version===m.destination_version&&x.kind===row.kind),'version-coverage-mismatch');if(row.is_latest)check(destination.some(x=>x.key===row.key&&x.version===m.destination_version&&x.is_latest),'destination-latest-version-mismatch');}
  const next=successor(catalog,mapping,sha(catalogBytes)),successorFile=path.join(defaults.state,'successor-catalog.json');
  const saved=await read(successorFile).catch(e=>{if(e.code==='ENOENT')return null;throw e;});
  if(!saved||!successorCompatible(saved,next,mapping))await save(successorFile,next);
  await save(path.join(defaults.state,core?'copy-core-receipt.json':'copy-all-receipt.json'),{at:new Date().toISOString(),scope:core?'surface-migration-prefix':'whole-research-bucket',versions:rows.length,bytes:rows.reduce((n,r)=>n+r.bytes,0),complete:true});
}
async function removeBridge() {
  await preflight(d);await policyPermissions();const expected=await read(policyFile),actual=await send(d,'GetBucketPolicy',destArgs);
  check(samePolicy(JSON.parse(actual.Policy),expected),'policy-changed-do-not-remove');
  await send(d,'DeleteBucketPolicy',destArgs);await save(path.join(defaults.state,'temporary-copy-policy-removal.json'),{at:new Date().toISOString(),removed:true});console.log('Temporary copy-only bridge removed');
}
const mode=process.argv[2];(async()=>{if(mode==='bridge')await bridge();else if(mode==='cancel-relay')await cancelRelay();else if(mode==='copy-core')await copy(true);else if(mode==='copy-all')await copy(false);else if(mode==='remove-bridge')await removeBridge();else throw Error();})().catch(async e=>{const r={at:new Date().toISOString(),mode,error:e.name,safe_reason:e.safeReason??null,http_status:e.$metadata?.httpStatusCode??null};await save(path.join(defaults.state,'server-copy-'+mode+'-failure.json'),r).catch(()=>{});console.error(JSON.stringify(r));process.exitCode=1;});
