import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import net from 'node:net';
import {fileURLToPath} from 'node:url';
import {fakeAWS,packetFixture,captured,original,mapping} from './website-derived-fixture.mjs';
import {pins,digest,hash,canonical,Lifecycle,Journal} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
import {loadPacket} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/packet.mjs';
import {adapterFor} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/lifecycle.mjs';
import {productionAWS} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/aws.mjs';
import {Collector,simulate,pages} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/collector.mjs';
import {freezePolicy} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/policy.mjs';

net.Socket.prototype.connect = function(){throw Error('REAL_SOCKET_FORBIDDEN');};
const audit=path.dirname(fileURLToPath(import.meta.url)), results=[];
function record(name,data){results.push({name,...data});fs.writeFileSync(path.join(audit,'independent-website-results.json'),JSON.stringify(results,null,2)+'\n');}
function expired(packet){try{packet.verify();return false;}catch(e){return /Expired|Stale/.test(e.message);}}
function setupRetire(f,p){
  f.o.bucket.controls=structuredClone(p.baseline.bucketControls);
  f.o.targetConfig=structuredClone(p.baseline.targetConfig);
  f.o.source.config.Aliases={Quantity:0};f.o.source.config.Enabled=false;
  f.o.targetCertificateDescription.InUseBy=['arn:aws:cloudfront::'+pins.destinationAccount+':distribution/'+pins.targetDistribution];
}

test('W1: real packet loader accepts wholly uncommitted evidence/gate fixtures',()=>{
  const p=packetFixture(), packet=loadPacket(p.options());packet.verify();
  assert.equal(p.g.evidenceCommit,undefined);assert.equal(p.g.gateCommit,undefined);
  assert.ok(!fs.existsSync(path.join(p.dir,'.git')));
  record('W1-uncommitted-packet-accepted',{reproduced:true,fixture:p.dir,gateSha256:p.options().rootGateSha256,phase:packet.authorization.phase});
});

test('W2: expiry during real SDK credential resolution still reaches physical mutation',async()=>{
  const p=packetFixture();let now=Date.now(),sends=0,atWireExpired=false;
  const packet=loadPacket({...p.options(),clock:()=>now}),f=fakeAWS();
  const aws=productionAWS({credentials:{source:async()=>{now=Date.parse(p.g.expiresAt)+1;return {accessKeyId:'SYNTHETIC',secretAccessKey:'SYNTHETIC'};},destination:{accessKeyId:'SYNTHETIC',secretAccessKey:'SYNTHETIC'}},
    requestHandler:{async handle(){sends++;atWireExpired=expired(packet);return {response:{statusCode:200,headers:{},body:Buffer.from('<UpdateDistributionResult/>')}};},destroy(){}}});
  f.aws.mutateOnce=(...a)=>aws.mutateOnce(...a);
  const adapter=adapterFor(f.aws,packet);
  const config=structuredClone(f.o.source.config);config.Aliases={Quantity:0};
  try{await adapter.mutateOnce('cloudfront','UpdateDistribution',{Id:pins.distribution,IfMatch:f.o.source.etag,DistributionConfig:config});}catch(e){assert.equal(sends,1);}
  finally{aws.destroy();}
  assert.equal(sends,1);assert.equal(atWireExpired,true);
  record('W2-expired-at-physical-send',{reproduced:true,fixture:p.dir,sends,atWireExpired,virtualClock:now,gateExpiresAt:p.g.expiresAt});
});

test('W3: retirement kernel returns observed after gate expires during final journal fsync',async()=>{
  const p=packetFixture('retire');let now=Date.now(),mutations=0;
  const packet=loadPacket({...p.options(),clock:()=>now});
  const sourceConfig=structuredClone(p.baseline.sourceConfig);sourceConfig.Aliases={Quantity:0};sourceConfig.Enabled=false;
  const o={sourceIdentity:{Account:pins.sourceAccount,Arn:pins.sourcePrincipal},destinationIdentity:{Account:pins.destinationAccount,Arn:pins.destinationPrincipal},
    target:{id:pins.targetDistribution,bucket:pins.targetBucket,status:'Deployed',enabled:true,issuedCertificate:pins.targetCertificate,certificateStatus:'ISSUED',certificate:pins.targetCertificate,aliases:pins.aliases},
    rootLiveProof:true,source:null,sourceAbsent:true,bucket:null,bucketAbsent:true,sourceObjects:[],targetObjects:p.baseline.targetObjects,
    certificateAbsent:false,sourceCertificate:{arn:pins.certificate,inUseBy:[],validationRecords:JSON.parse(JSON.stringify(p.baseline.sourceCertificateDescription.DomainValidationOptions.map(x=>x.ResourceRecord))).filter((x,i,a)=>a.findIndex(y=>canonical(y)===canonical(x))===i).sort((a,b)=>a.Name<b.Name?-1:1)},
    producersStopped:true,writeFreezeEnforced:true,freezeControlHash:p.g.freezeControlHash,
    allowed:['acm:DeleteCertificate'],permissions:[{action:'acm:DeleteCertificate',resource:pins.certificate,decision:'allowed'}]};
  assert.equal(digest(o.sourceCertificate.validationRecords),p.baseline.sourceValidationRecordsHash);
  const adapter={verifyBindings:packet.verify,async observe(){return {...structuredClone(o),observedAt:now};},async mutateOnce(){mutations++;o.certificateAbsent=true;o.sourceCertificate=null;}};
  const journal=new Journal(p.g.journalPath),append=journal.append.bind(journal);
  journal.append=e=>{append(e);if(e.state==='observed')now=Date.parse(p.g.expiresAt)+1;};
  const runner=new Lifecycle({adapter,journal,baseline:packet.baseline,bundle:packet.bundle,authorization:packet.authorization,clock:()=>now});
  const state=await runner.run('retire','certificate');
  assert.equal(state,'observed');assert.equal(expired(packet),true);assert.equal(mutations,1);
  record('W3-success-returned-after-terminal-expiry',{reproduced:true,fixture:p.dir,state,mutations,expiredOnReturn:expired(packet)});
});

for(const resource of ['bucket','certificate'])test('W4: collector misses source '+resource+' recreation during closing dependencies',async()=>{
  const p=packetFixture('retire'),packet=loadPacket(p.options()),f=fakeAWS();setupRetire(f,p);
  f.o.source=null;f.o.sourceObjects=[];let recreated=false;
  const originalRead=f.aws.read;
  f.aws.read=async(side,service,command,input)=>{
    if(side==='source' && service==='s3'){
      if(command==='ListBuckets')return {Buckets:resource==='bucket'&&recreated?[{Name:pins.bucket,CreationDate:new Date()}]:[]};
      if(command==='HeadBucket'){if(resource==='bucket'&&recreated)return {};const e=Error();e.name='NotFound';throw e;}
    }
    if(side==='source'&&service==='acm'){
      if(command==='ListCertificates')return {CertificateSummaryList:resource==='certificate'&&recreated?[{DomainName:'quantyra.org',CertificateArn:pins.certificate}]:[]};
      if(command==='DescribeCertificate'&&!(resource==='certificate'&&recreated)){const e=Error();e.name='ResourceNotFoundException';throw e;}
    }
    return originalRead(side,service,command,input);
  };
  const collector=new Collector({aws:f.aws,packet,original,mapping,dnsProof:async()=>({verified:true}),liveProof:async()=>{recreated=true;return {verified:true};}});
  const o=await collector.observe({step:'certificate'});
  assert.equal(recreated,true);assert.equal(resource==='bucket'?o.bucketAbsent:o.certificateAbsent,true);
  record('W4-stale-source-'+resource+'-absence',{reproduced:true,fixture:p.dir,reportedAbsent:true,resourceRecreatedDuringSweep:true,lastSourceCalls:f.calls.filter(c=>c.side==='source').slice(-8)});
});

test('W5: IAM resource-level deny/missing context is discarded despite action-level allow',async()=>{
  const resource='arn:aws:s3:::'+pins.bucket+'/'+original[0].key;
  const aws={read:async()=>({IsTruncated:false,EvaluationResults:[{EvalActionName:'s3:DeleteObjectVersion',EvalResourceName:resource,EvalDecision:'allowed',ResourceSpecificResults:[{EvalResourceName:resource,EvalResourceDecision:'explicitDeny',MissingContextValues:['s3:VersionId']}]}]})};
  const r=await simulate(aws,'DeleteObject',resource,null,[{ContextKeyName:'s3:VersionId',ContextKeyType:'string',ContextKeyValues:['null']}]);
  assert.equal(r.decision,'allowed');record('W5-denied-resource-result-accepted',{reproduced:true,returned:r});
});

test('W6: unversioned source freeze explicitly denies required DeleteObject while preflight maps only DeleteObjectVersion',async()=>{
  assert.equal(captured.baseline.bucketControls.GetBucketVersioning.Status,undefined);
  const policy=freezePolicy(captured.baseline.originalBucketPolicy,original);
  const deny=policy.Statement.find(s=>s.Sid==='LifecycleDenyAllNonReadExceptVersionCleanup');
  assert.equal(deny.NotAction.includes('s3:DeleteObject'),false);
  let sent;
  const resource='arn:aws:s3:::'+pins.bucket+'/'+original[0].key;
  const aws={read:async(s,v,c,i)=>{sent=i;return {IsTruncated:false,EvaluationResults:[{EvalActionName:i.ActionNames[0],EvalResourceName:resource,EvalDecision:'allowed'}]};}};
  await simulate(aws,'DeleteObject',resource,policy,[{ContextKeyName:'s3:VersionId',ContextKeyType:'string',ContextKeyValues:['null']}]);
  assert.deepEqual(sent.ActionNames,['s3:DeleteObjectVersion']);
  record('W6-unversioned-delete-permission-mismatch',{reproduced:true,bucketVersioning:captured.baseline.bucketControls.GetBucketVersioning,denyNotAction:deny.NotAction,simulatedActions:sent.ActionNames,documentation:'https://docs.aws.amazon.com/AmazonS3/latest/userguide/DeletingObjects.html',liveDeletionAttempted:false});
});

test('negative control: expired packet blocks adapter before mutation begins',async()=>{
  const p=packetFixture(),now=Date.parse(p.g.expiresAt)+1;
  assert.throws(()=>loadPacket({...p.options(),clock:()=>now}),/Expired|Stale/);
  record('negative-control-expired-loader-blocked',{passed:true,fixture:p.dir});
});
