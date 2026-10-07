// Isolated metadata-only destination control. Never imports executing migration tools.
import * as fs from 'node:fs/promises';
import {createReadStream} from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {createHash,randomUUID} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import * as S3 from '@aws-sdk/client-s3';
import {STSClient,GetCallerIdentityCommand} from '@aws-sdk/client-sts';
import {IAMClient,SimulatePrincipalPolicyCommand} from '@aws-sdk/client-iam';
import {fromIni} from '@aws-sdk/credential-providers';
import {ACCOUNT,BUCKET,SOURCE,PACKET_HASH,sha,same,policy,policyHash,rootGate,validateControls,validateBoundary,ensurePolicy,requireThat as check} from './control.mjs';
const state=path.join(os.homedir(),'.quantyra/aws-migration-20261006'),out=path.join(state,'security-20261007');
const cfg={region:'us-east-1',credentials:fromIni({profile:'quantyra'}),maxAttempts:3};
const readClient=new S3.S3Client(cfg),writeClient=new S3.S3Client({...cfg,maxAttempts:1});
const args={Bucket:BUCKET,ExpectedBucketOwner:ACCOUNT};
const readJson=async f=>JSON.parse(await fs.readFile(f,'utf8'));
const hashFile=async f=>{const h=createHash('sha256');for await(const b of createReadStream(f))h.update(b);return h.digest('hex');};
const absent=async f=>{try{await fs.stat(f);return false;}catch(e){if(e.code==='ENOENT')return true;throw e;}};
const alive=pid=>{try{process.kill(pid,0);return true;}catch(e){check(e.code==='ESRCH','process-absence-not-authoritative');return false;}};
const send=(name,input=args)=>readClient.send(new S3[name+'Command'](input));
async function getPolicy(){try{return JSON.parse((await send('GetBucketPolicy')).Policy);}catch(e){if(e.name==='NoSuchBucketPolicy')return null;throw e;}}
async function controls(){
  const identity=await new STSClient(cfg).send(new GetCallerIdentityCommand({}));
  const [location,versioning,blocks,ownership,encryption,acl]=await Promise.all(['GetBucketLocation','GetBucketVersioning','GetPublicAccessBlock','GetBucketOwnershipControls','GetBucketEncryption','GetBucketAcl'].map(n=>send(n)));
  const x={identity:{Account:identity.Account,Arn:identity.Arn},expected_owner:ACCOUNT,bucket:BUCKET,region:location.LocationConstraint??'us-east-1',versioning:{Status:versioning.Status,...(versioning.MFADelete?{MFADelete:versioning.MFADelete}:{})},public_blocks:blocks.PublicAccessBlockConfiguration,ownership:ownership.OwnershipControls,encryption:encryption.ServerSideEncryptionConfiguration,acl:{Owner:{ID:acl.Owner?.ID},Grants:acl.Grants?.map(g=>({Permission:g.Permission,Grantee:{Type:g.Grantee?.Type,ID:g.Grantee?.ID}}))}};
  validateControls(x);return x;
}
async function permissions(){const actions=['s3:GetBucketPolicy','s3:PutBucketPolicy'];const r=await new IAMClient(cfg).send(new SimulatePrincipalPolicyCommand({PolicySourceArn:`arn:aws:iam::${ACCOUNT}:user/ServiceAdmin`,ActionNames:actions,ResourceArns:[`arn:aws:s3:::${BUCKET}`]}));check(!r.IsTruncated&&r.EvaluationResults?.length===2&&actions.every(a=>r.EvaluationResults.some(x=>x.EvalActionName===a&&x.EvalDecision==='allowed')),'policy-permission-required');return r.EvaluationResults.map(x=>({action:x.EvalActionName,decision:x.EvalDecision}));}
async function boundary(hashPins=true){
  const packetFile=path.join(state,'repair/fullscope-packet.json'),bytes=await fs.readFile(packetFile),packet=JSON.parse(bytes),packetHash=sha(bytes);
  const bridgeFile=path.join(state,'repair/temporary-copy-policy-removal.json'),bridge=await readJson(bridgeFile),status=await readJson(path.join(state,'repair/control-status.json'));
  const locks=!(await absent(path.join(state,'repair/control.lock')))||!(await absent(path.join(state,'repair/writer.lock')));
  const b={alive:alive(13356)||alive(6852),locks,status,packet,packetHash,bridge,bridgeHash:await hashFile(bridgeFile)};validateBoundary(b);
  if(hashPins){
    const permittedRoots=[state,path.join(os.homedir(),'.quantyra/archive-catalogs'),path.resolve(new URL('..',import.meta.url).pathname.replace(/^\/([A-Za-z]:)/,'$1'))];
    check(packet.artifacts.length===305,'unexpected-packet-pin-count');
    for(const pin of packet.artifacts){const f=path.resolve(pin.file);check(permittedRoots.some(r=>f.startsWith(path.resolve(r)+path.sep))&&!/credentials|\.key$/i.test(f),'unsafe-packet-pin-path');check(/^[a-f0-9]{64}$/.test(pin.sha256)&&await hashFile(f)===pin.sha256,'immutable-packet-pin-mismatch');}
    for(const c of packet.catalogs)check(packet.artifacts.some(a=>a.file===c.catalog_file&&a.sha256===c.catalog_sha256),'catalog-pin-missing');
  }
  return {controller_pid:13356,controller_absent:true,writer_absent:true,locks_absent:true,phase:status.phase,fullscopepacket_sha256:packetHash,pins_checked:hashPins?packet.artifacts.length:0,bridge_removal_sha256:b.bridgeHash};
}
async function protectedDirectory(){await fs.mkdir(out,{recursive:true,mode:0o700});if(process.platform==='win32'){const user=execFileSync('whoami',[],{encoding:'utf8',windowsHide:true}).trim();execFileSync('icacls',[out,'/inheritance:r','/grant:r',`${user}:(OI)(CI)F`,'SYSTEM:(OI)(CI)F'],{stdio:'ignore',windowsHide:true});}}
const immutable=async (name,value)=>{const file=path.join(out,name);await fs.writeFile(file,JSON.stringify(value,null,2)+'\n',{flag:'wx',mode:0o600});return {file,sha256:await hashFile(file)};};
async function codePins(){const r={};for(const n of ['control.mjs','cli.mjs','test.mjs','README.md'])r[n]=await hashFile(new URL(n,import.meta.url));return r;}
async function main(){
  const mode=process.argv[2];check(['check','apply'].includes(mode),'mode-check-or-apply-required');await protectedDirectory();
  const run=new Date().toISOString().replace(/[^0-9TZ]/g,'')+'-'+randomUUID(),code=await codePins();
  if(mode==='check'){
    const current=await getPolicy(),metadata=await controls();let gate;
    try{gate={ready:true,...await boundary()};}catch(e){gate={ready:false,reason:e.safeReason??'boundary-evidence-unavailable'};}
    const evidence={type:'archive-https-readonly-check-v1',at:new Date().toISOString(),metadata,policy_present:current!==null,policy:current,owned_https_baseline:same(current,policy),source_or_migration_grants_present:current?.Statement?.some(s=>s.Effect==='Allow')??false,boundary:gate,code_sha256:code,cloud_mutations:0,source_eligibility:'HOLD'};
    const receipt=await immutable(`check-${run}.json`,evidence);console.log(JSON.stringify({mode,...receipt,boundary:gate,owned_https_baseline:evidence.owned_https_baseline,cloud_mutations:0}));return;
  }
  const lock=path.join(out,'apply.lock');const handle=await fs.open(lock,'wx',0o600);await handle.writeFile(JSON.stringify({pid:process.pid,at:new Date().toISOString()}));await handle.close();
  try{
    const before=await controls(),permission=await permissions(),bound=await boundary();
    const priorIntent=(await fs.readdir(out)).some(n=>n.startsWith('put-intent-'));
    const result=await ensurePolicy({get:getPolicy,put:p=>writeClient.send(new S3.PutBucketPolicyCommand({...args,Policy:JSON.stringify(p)})),priorIntent,boundary:async()=>{await boundary();check(same(await controls(),before),'controls-changed-before-apply');},prepare:()=>immutable(`put-intent-${run}.json`,{type:'archive-https-put-intent-v1',at:new Date().toISOString(),...bound,expected_owner:ACCOUNT,bucket:BUCKET,policy,policy_sha256:policyHash(),code_sha256:code,sdk_max_attempts:1})});
    const after=await controls();check(same(before,after),'destination-controls-changed');
    const final=await getPolicy();const proof=rootGate(final);const finalBound=await boundary();
    const publicStatus=await send('GetBucketPolicyStatus');check(publicStatus.PolicyStatus?.IsPublic===false,'policy-public-status-unexpected');
    const supplement={type:'archive-destination-https-security-supplement-v1',at:new Date().toISOString(),complete:true,original_fullscopepacket_sha256:PACKET_HASH,...finalBound,expected_owner:ACCOUNT,bucket:BUCKET,principal:after.identity,operation:result.operation,sdk_mutation_attempts:result.sdk_mutation_attempts,lost_reply:result.lost_reply,policy:final,finalpolicy_sha256:sha(JSON.stringify(final)),readback_sha256:sha(JSON.stringify({policy:final,metadata:after,proof,public:false})),readback:{metadata:after,...proof,public:false},permissions:permission,code_sha256:code,source_mutations:0,original_packet_unchanged:true,root_acceptance:false,source_eligibility:'HOLD'};
    const receipt=await immutable(`security-supplement-${run}.json`,supplement);console.log(JSON.stringify({mode,...receipt,original_fullscopepacket_sha256:PACKET_HASH,finalpolicy_sha256:supplement.finalpolicy_sha256,readback_sha256:supplement.readback_sha256,operation:result.operation,sdk_mutation_attempts:result.sdk_mutation_attempts,...proof,source_eligibility:'HOLD'}));
  }finally{await fs.unlink(lock);}
}
main().catch(e=>{console.error(JSON.stringify({status:'security-control-refused-or-unproven',safe_reason:e.safeReason??'metadata-or-sdk-operation-failed',error:e.name,http_status:e.$metadata?.httpStatusCode??null}));process.exitCode=1;});
