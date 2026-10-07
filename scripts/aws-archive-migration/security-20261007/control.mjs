import {createHash} from 'node:crypto';
export const ACCOUNT='063280428495';
export const BUCKET='quantyra-research-archive-063280428495-us-east-1';
export const SOURCE='quantyra-research-archive-485386182336-us-east-1';
export const PACKET_HASH='713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce';
export const sha=x=>createHash('sha256').update(x).digest('hex');
export function requireThat(ok,reason){if(!ok)throw Object.assign(new Error(reason),{safeReason:reason});}
const canonical=x=>Array.isArray(x)?x.map(canonical):x&&typeof x==='object'?Object.fromEntries(Object.keys(x).sort().map(k=>[k,canonical(x[k])])):x;
export const same=(a,b)=>JSON.stringify(canonical(a))===JSON.stringify(canonical(b));
export const policy={Version:'2012-10-17',Statement:[{Sid:'QuantyraArchiveHTTPSOnly20261007',Effect:'Deny',Principal:'*',Action:'s3:*',Resource:[`arn:aws:s3:::${BUCKET}`,`arn:aws:s3:::${BUCKET}/*`],Condition:{Bool:{'aws:SecureTransport':'false'}}}]};
export const policyHash=()=>sha(JSON.stringify(policy));
export function rootGate(p){requireThat(same(p,policy),'destination-https-baseline-required');return {https_deny:true,source_migration_grants:false,statements:1};}
export function validateControls(x){
  requireThat(x.identity.Account===ACCOUNT&&x.identity.Arn===`arn:aws:iam::${ACCOUNT}:user/ServiceAdmin`,'unexpected-destination-principal');
  requireThat(x.region==='us-east-1','unexpected-destination-region');
  requireThat(x.versioning.Status==='Enabled'&&!x.versioning.MFADelete,'versioning-control-changed');
  requireThat(['BlockPublicAcls','IgnorePublicAcls','BlockPublicPolicy','RestrictPublicBuckets'].every(k=>x.public_blocks[k]===true),'public-blocks-required');
  requireThat(same(x.ownership,{Rules:[{ObjectOwnership:'BucketOwnerEnforced'}]}),'owner-enforcement-required');
  requireThat(x.encryption.Rules?.length===1&&x.encryption.Rules[0].ApplyServerSideEncryptionByDefault?.SSEAlgorithm==='AES256','aes256-required');
  requireThat(x.acl.Grants?.length===1&&x.acl.Grants[0].Permission==='FULL_CONTROL'&&x.acl.Grants[0].Grantee?.Type==='CanonicalUser'&&x.acl.Grants[0].Grantee.ID===x.acl.Owner?.ID,'private-owner-acl-required');
  return true;
}
export function validateBoundary({alive,locks,status,packet,packetHash,bridge,bridgeHash}){
  requireThat(!alive&&!locks,'controller-or-writer-live');
  requireThat(status.pid===13356&&status.phase==='author-complete-awaiting-root-acceptance'&&status.packet_sha256===packetHash,'authoritative-controller-completion-required');
  requireThat(packetHash===PACKET_HASH&&packet.type==='archive-author-fullscope-v1'&&packet.complete===true&&packet.versions===205&&packet.core_chunks===51&&packet.recovery_unique_chunks===54&&packet.recovery_catalogs===44&&packet.catalogs?.length===45&&packet.restore?.verified===true&&packet.restore.bucket===BUCKET&&packet.bridge?.absent===true,'bound-full205-packet-required');
  requireThat(bridge.absent===true&&same(bridge,packet.bridge)&&packet.artifacts.some(x=>x.file.replaceAll('\\','/').endsWith('/repair/temporary-copy-policy-removal.json')&&x.sha256===bridgeHash),'bound-bridge-removal-required');
}
export async function ensurePolicy({get,put,boundary,prepare,priorIntent=false}){
  await boundary();const before=await get();
  requireThat(before===null||same(before,policy),'unexpected-unrelated-policy');
  if(before!==null){rootGate(before);return {operation:'conditional-noop',sdk_mutation_attempts:0,lost_reply:false,readback:before};}
  requireThat(!priorIntent,'prior-mutation-intent-requires-readback-only');
  await prepare();await boundary();
  requireThat(await get()===null,'policy-changed-before-mutation');
  let lost=false;try{await put(policy);}catch{lost=true;}
  const after=await get();rootGate(after);
  return {operation:'installed',sdk_mutation_attempts:1,lost_reply:lost,readback:after};
}
