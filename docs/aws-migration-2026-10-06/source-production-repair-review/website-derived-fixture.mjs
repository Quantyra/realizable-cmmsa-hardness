import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {pins,hash,digest,canonical,requirements,Lifecycle,Journal} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
import {loadPacket,reader,toolingHash,root,validateEvidence,currentCommit} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/packet.mjs';
import {productionAWS} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/aws.mjs';
import {Collector,pages,collectBucket,simulate,simulateDelete} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/collector.mjs';
import {freezePolicy,nameGuard} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/policy.mjs';
import {main,adapterFor} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/lifecycle.mjs';
import {dnsProof,liveProof} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/proofs.mjs';
import {mutationWire} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/wire.mjs';
import {Readable} from 'node:stream';
import {spawnSync} from 'node:child_process';
const captured=JSON.parse(fs.readFileSync(path.join(root,'evidence/source-lifecycle-completion-2026-10-07/preflight-initial.json')));
const original=captured.baseline.objects;
const staged=JSON.parse(fs.readFileSync(path.join(root,'evidence/route53-2026-10-06/record-plan.json'))).records;
const mapping=JSON.parse(fs.readFileSync(path.join(root,'evidence/aws-migration-2026-10-06/version-mapping.json')));
function fakeAWS() {
  const o=structuredClone(captured.observation);let mutations=0;
  const calls=[];const ns=['ns-1077.awsdns-06.org','ns-1890.awsdns-44.co.uk','ns-252.awsdns-31.com','ns-606.awsdns-11.net'];
  o.targetCertificateDescription.Status='ISSUED';
  o.targetCertificateDescription.NotBefore=new Date(Date.now()-100000).toISOString();o.targetCertificateDescription.NotAfter=new Date(Date.now()+86400000).toISOString();
  const aws={
    async identify(){return {sourceIdentity:o.sourceIdentity,destinationIdentity:o.destinationIdentity};},
    async read(side,service,command,i={}) {
      calls.push({side,service,command});
      if(service==='s3') {
        const src=side==='source',rows=src?o.sourceObjects:o.targetObjects,controls=src?o.bucket.controls:o.targetControls;
        if(command==='ListBuckets')return {Buckets:[{Name:src?pins.bucket:pins.targetBucket,CreationDate:new Date(o.bucket.creationDate)}]};
        if(command==='HeadBucket')return {};
        if(command==='ListObjectsV2')return {Contents:rows.map(x=>({Key:x.key,Size:x.bytes,ETag:src?x.etag:x.destinationETag,LastModified:new Date(src?x.lastModified:x.destinationLastModified)})),IsTruncated:false};
        if(command==='ListObjectVersions')return src?{Versions:rows.map(x=>({Key:x.key,VersionId:'null',IsLatest:true})),IsTruncated:false}:{Versions:o.targetVersions.map(({kind,...x})=>x),IsTruncated:false};
        if(command==='ListMultipartUploads')return {IsTruncated:false};
        if(command==='GetObjectTagging')return {TagSet:rows.find(x=>x.key===i.Key).tags};
        if(command==='GetObject') {
          const x=rows.find(x=>x.key===i.Key),b=fs.readFileSync(path.join(root,'.migration-cache',x.sha256));
          return {...x.metadata,ContentLength:x.bytes,ETag:src?x.etag:x.destinationETag,LastModified:new Date(src?x.lastModified:x.destinationLastModified),ServerSideEncryption:x.sourceEncryption,...(!src?{VersionId:x.destinationVersion}:{}),Body:[b]};
        }
        const c=controls[command];assert.ok(c,'unmocked s3 read '+command);
        if(c.absent){const e=Error('expected absence');e.name=c.absent;throw e;}return c;
      }
      if(service==='cloudfront') {
        const d=side==='source'?o.source:{id:pins.targetDistribution,status:'Deployed',etag:'target',config:o.targetConfig};
        if(command==='ListDistributions')return {DistributionList:{Items:d?[{Id:d.id,Origins:d.config.Origins}]:[],IsTruncated:false}};
        if(!d){const e=Error();e.name='NoSuchDistribution';throw e;}
        return command==='GetDistribution'?{Distribution:{Id:d.id,Status:d.status,DistributionConfig:d.config},ETag:d.etag}:{DistributionConfig:d.config,ETag:d.etag};
      }
      if(service==='acm') {
        if(command==='ListCertificates')return {CertificateSummaryList:[{DomainName:'*.quantyra.org',CertificateArn:pins.certificate}]};
        return {Certificate:side==='source'?o.sourceCertificate.description:o.targetCertificateDescription};
      }
      if(service==='iam') {
        if(command==='GetUserPolicy')return {PolicyDocument:encodeURIComponent(JSON.stringify(nameGuard))};
        const decision=i.ActionNames[0]==='s3:CreateBucket'||i.ActionNames[0]==='s3:PutObject'&&i.ResourcePolicy?.includes('LifecycleDeny')?'explicitDeny':'allowed';
        return {IsTruncated:false,EvaluationResults:[{EvalActionName:i.ActionNames[0],EvalResourceName:i.ResourceArns[0],EvalDecision:decision,ResourceSpecificResults:[{EvalResourceName:i.ResourceArns[0],EvalResourceDecision:decision}]}]};
      }
      if(service==='route53') {
        if(command==='GetHostedZone')return {HostedZone:{Id:pins.zone,Name:'quantyra.org.',Config:{PrivateZone:false}},DelegationSet:{NameServers:ns}};
        if(command==='ListTagsForResource')return {ResourceTagSet:{Tags:[{Key:'DestinationAccount',Value:pins.destinationAccount},{Key:'MigrationStory',Value:'S3157'}]}};
        return {ResourceRecordSets:staged,IsTruncated:false};
      }
      throw Error('UnexpectedFixtureRead');
    },
    async mutateOnce(service,command,input,authorize){authorize();mutations++;if(command==='UpdateDistribution'){o.source.config=structuredClone(input.DistributionConfig);o.source.etag='updated';}else throw Error('UnexpectedFixtureMutation');},
    destroy(){}
  };return {aws,o,calls,mutations:()=>mutations,ns};
}
function packetFixture(phase='release') {
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'website-production-packet-'));const now=Date.now();
  const git=(args)=>{const r=spawnSync('git',args,{cwd:dir,encoding:'utf8'});assert.equal(r.status,0,r.stderr);return r.stdout.trim();};
  git(['init','-q']);git(['config','user.name','Synthetic Root']);git(['config','user.email','fixture@invalid']);
  fs.mkdirSync(path.join(dir,'docs/aws-migration-2026-10-06'),{recursive:true});
  function write(name,value) {const b=Buffer.from(JSON.stringify(value));fs.writeFileSync(path.join(dir,name),b);return {path:name,sha256:hash(b)};}
  const baseline=structuredClone(captured.baseline);
  if(phase==='retire') {
    baseline.bucketControls.policy=freezePolicy(baseline.originalBucketPolicy,original);baseline.bucketControls.GetBucketPolicy={Policy:canonical(baseline.bucketControls.policy)};baseline.bucketControlsHash=digest(baseline.bucketControls);
    baseline.targetConfig.Aliases={Quantity:2,Items:pins.aliases};baseline.targetConfig.ViewerCertificate={CloudFrontDefaultCertificate:false,ACMCertificateArn:pins.targetCertificate,SSLSupportMethod:'sni-only',MinimumProtocolVersion:'TLSv1.2_2021'};
  }
  const b=write('baseline.json',baseline);
  const review=write('review.json',{verdict:'GO',independent:true,reviewer:'independent-reviewer',author:'implementation-owner',toolingHash:toolingHash(),commit:currentCommit(),resources:pins});
  const evidence={},evidenceFiles={};
  for(const name of requirements[phase]) {
    const receipt={schema:1,kind:name,resources:pins,observedAt:now,expiresAt:now+240000,observer:'actual-owning-operator',method:'authenticated observed test fixture',coverage:{resource:'full scope'},checks:[{id:'fact',observed:'verified',expected:'verified'}]};
    if(name==='completeDNS'){receipt.recordPlan=write('record-plan.json',{completeSourceInventory:true,sourceExportSha256:'export-hash',records:staged});receipt.sourceExport=write('source-export.json',{complete:true,sha256:'export-hash',records:staged.filter(r=>r.ResourceRecords)});}
    if(name==='sourceProducerShutdown') {
      receipt.inventoryComplete=true;receipt.inventory=[{id:'all-source-publishers',owner:'source-owner',kind:'external'}];receipt.inventoryHash=digest(receipt.inventory);
      const control=write('production-shutdown-control.json',{producerId:'all-source-publishers',state:'DISABLED',observer:'source-owner',method:'actual controller/schedule read',controlId:'source-controller',observed:'DISABLED',expected:'DISABLED',observedAt:now,expiresAt:now+240000});
      const proof=write('production-shutdown-proof.json',{producerId:'all-source-publishers',owner:'source-owner',state:'DISABLED',observer:'source-owner',controlEvidence:control,observedAt:now,expiresAt:now+240000});
      receipt.shutdown=[{id:'all-source-publishers',owner:'source-owner',state:'DISABLED',mechanism:'disabled source controller',proof,observedAt:now,expiresAt:now+240000}];
    }
    if(name==='sourceWriteQuiescence') {
      receipt.policyHash=digest(baseline.bucketControls.policy);receipt.nameGuardHash=digest(nameGuard);
      receipt.rootOverrideCustody=write('root-custody.json',{owner:'source-owner',observer:'independent-owner',method:'actual source root access custody hold',controlEvidence:{holdId:'root-held'},principal:'arn:aws:iam::'+pins.sourceAccount+':root',state:'CHANGE_HOLD',observedAt:now,expiresAt:now+240000});
      receipt.creatorShutdownProof={path:'sourceProducerShutdown-receipt.json',sha256:hash(fs.readFileSync(path.join(dir,'sourceProducerShutdown-receipt.json')))};
    }
    if(name==='fullCustomDomainLive')receipt.routeProbes=[{host:'quantyra.org',uri:'/mission/?review=1',key:'mission/index.html',status:200}];
    const r=write(name+'-receipt.json',receipt);
    const payload={schema:1,kind:name,owner:'root',accepted:true,resources:pins,observedAt:now,expiresAt:now+240000,receipts:[r]};
    evidenceFiles[name]=write(name+'-acceptance.json',payload);evidence[name]=digest(payload);
  }
  const journalPath=path.join(dir,'execution.jsonl');
  const g={schema:1,enabled:true,phase,rootAuthorization:{owner:'root',approved:true},independentReview:{verdict:'GO',toolingHash:toolingHash()},resources:pins,toolingHash:toolingHash(),baselineHash:digest(baseline),baseline:b,review,evidence,evidenceFiles,issuedAt:new Date(now-1000).toISOString(),expiresAt:new Date(now+240000).toISOString(),journalPath,journalBinding:{prefixBytes:0,sha256:hash('')}};
  if(phase==='retire')g.freezeControlHash=digest(baseline.bucketControls.policy);
  const gate=write('gate.json',g);
  return {dir,g,baseline,write,options:()=>{
    g.rootAllowlist=write('docs/aws-migration-2026-10-06/website-source-production-allowlist.json',{schema:1,owner:'root',accepted:true,resources:pins,baseline:g.baseline,evidenceFiles:g.evidenceFiles,review:g.review});
    git(['add','--','*.json',':!gate.json']);git(['commit','-q','--allow-empty','-m','Synthetic immutable evidence']);const evidenceCommit=git(['rev-parse','HEAD']);
    g.rootEvidenceCommit=evidenceCommit;write('gate.json',g);git(['add','gate.json']);git(['commit','-q','-m','Synthetic separate gate']);const gateCommit=git(['rev-parse','HEAD']);
    return {gatePath:path.join(dir,'gate.json'),rootGateSha256:hash(fs.readFileSync(path.join(dir,'gate.json'))),reviewSha256:review.sha256,rootRepository:dir,evidenceCommit,gateCommit};
  },cleanup:()=>fs.rmSync(dir,{recursive:true,force:true})};
}
export {fakeAWS,packetFixture,captured,original,mapping};
