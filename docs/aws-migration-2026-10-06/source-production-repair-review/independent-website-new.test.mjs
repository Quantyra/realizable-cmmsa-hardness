import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {EventEmitter} from 'node:events';
import {fakeAWS,packetFixture,captured,original,mapping} from './website-derived-fixture.mjs';
import {pins,digest,hash,canonical} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
import {loadPacket} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/packet.mjs';
import {Collector} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/collector.mjs';
import {productionAWS} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/aws.mjs';
import {physicalHTTP} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/physical-http.mjs';
import {adapterFor} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/lifecycle.mjs';
import {sourceCertificateAbsent} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/dns-cleanup.mjs';
const here=path.dirname(fileURLToPath(import.meta.url)),results=[];
function record(name,data){results.push({name,...data});fs.writeFileSync(path.join(here,'independent-website-new-results.json'),JSON.stringify(results,null,2)+'\n');}

test('R1 real committed loader accepts 200 freeze transition and refuses otherwise identical service-observed 204',()=>{
  const p=packetFixture('retire'),before={creationDate:p.baseline.bucketCreationDate,policyHash:digest(p.baseline.originalBucketPolicy),objectsHash:digest(original)};
  p.baseline.bucketCreationDate='2026-10-07T13:00:00.000Z';p.g.baseline=p.write('baseline.json',p.baseline);p.g.baselineHash=digest(p.baseline);
  const after={creationDate:p.baseline.bucketCreationDate,policyHash:digest(p.baseline.bucketControls.policy),objectsHash:digest(original)};
  const request={operation:'PutBucketPolicy',bucket:pins.bucket,policyHash:after.policyHash,principal:pins.sourcePrincipal,requestId:'synthetic-204-service-contract',httpStatusCode:200};
  const install=status=>{request.httpStatusCode=status;const journal=p.write('freeze-installation-journal.json',{before,after,requests:[request]});p.g.bucketIdentityTransition=p.write('bucket-transition.json',{schema:1,owner:'root',accepted:true,resources:pins,before,after,observer:'independent-continuity-owner',ownerObservedContinuity:true,installationJournal:journal});return p.options();};
  const accepted=install(200);assert.ok(loadPacket(accepted));const rejected=install(204);
  assert.throws(()=>loadPacket(rejected),/SourceFreezeOnlyInstallationJournalRequired/);
  record('R1-successful-204-freeze-transition-rejected',{reproduced:true,fixture:p.dir,accepted_200_commits:{evidence:accepted.evidenceCommit,gate:accepted.gateCommit},rejected_204_commits:{evidence:rejected.evidenceCommit,gate:rejected.gateCommit},actual_response_status:204,reason:'SourceFreezeOnlyInstallationJournalRequired'});
});

for(const mode of ['expiry','bound-bytes'])test('W2 warmed actual SDK signer and authenticated TLS '+mode+' reject before req.end',async()=>{
  const p=packetFixture();let now=Date.now(),resolutions=0,ends=0;
  const packet=loadPacket({...p.options(),clock:()=>now});
  const physical=physicalHTTP({request:()=>{
    const req=new EventEmitter();req.end=()=>{ends++;req.emit('close');};req.destroy=e=>{req.emit('error',e);req.emit('close');};
    queueMicrotask(()=>{const socket=new EventEmitter();socket.authorized=true;req.emit('socket',socket);
      if(mode==='expiry')now=Date.parse(p.g.expiresAt)+1;else fs.appendFileSync(path.join(p.dir,'baseline.json'),' ');
      socket.emit('secureConnect');});return req;
  }});
  const provider=async()=>{resolutions++;return {accessKeyId:'SYNTHETIC_SOURCE',secretAccessKey:'SYNTHETIC'};};
  const aws=productionAWS({credentials:{source:provider,destination:{accessKeyId:'SYNTHETIC_DEST',secretAccessKey:'SYNTHETIC'}},requestHandler:{
    handleAuthorized:(...a)=>physical.handleAuthorized(...a),
    async handle(r){assert.ok(r.hostname.startsWith('sts.'));const source=r.headers.authorization.includes('SYNTHETIC_SOURCE');return {response:{statusCode:200,headers:{'content-type':'text/xml'},body:Buffer.from('<GetCallerIdentityResponse xmlns="https://sts.amazonaws.com/doc/2011-06-15/"><GetCallerIdentityResult><Account>'+(source?pins.sourceAccount:pins.destinationAccount)+'</Account><Arn>'+(source?pins.sourcePrincipal:pins.destinationPrincipal)+'</Arn><UserId>SYNTHETIC</UserId></GetCallerIdentityResult></GetCallerIdentityResponse>')}};},destroy(){}}});
  try{await aws.identify();assert.equal(resolutions,1);const f=fakeAWS();f.aws.mutateOnce=(...a)=>aws.mutateOnce(...a);const adapter=adapterFor(f.aws,packet),config=structuredClone(f.o.source.config);config.Aliases={Quantity:0};
    await assert.rejects(adapter.mutateOnce('cloudfront','UpdateDistribution',{Id:pins.distribution,IfMatch:f.o.source.etag,DistributionConfig:config}),/Expired|Stale|BoundReceiptChanged/);
    assert.equal(ends,0);assert.equal(resolutions,1);record('W2-warmed-TLS-'+mode+'-rejected',{passed:true,fixture:p.dir,credentialResolutions:resolutions,physicalHttpEnds:ends});
  }finally{aws.destroy();}
});

for(const kind of ['EC_prime256v1','www-primary','truncated-SAN'])test('R2 closing collector accepts undisclosed related certificate '+kind,async()=>{
  const f=fakeAWS(),read=f.aws.read,inputs=[];let introduced=false;
  const extra={CertificateArn:'arn:aws:acm:us-east-1:'+pins.sourceAccount+':certificate/11111111-2222-4333-8444-555555555555',DomainName:kind==='www-primary'?'www.quantyra.org':kind==='truncated-SAN'?'unrelated.example.org':'quantyra.org',KeyAlgorithm:kind==='EC_prime256v1'?'EC_prime256v1':'RSA_2048',SubjectAlternativeNameSummaries:kind==='truncated-SAN'?Array.from({length:100},(_,i)=>'name'+i+'.example.org'):[kind==='www-primary'?'www.quantyra.org':'quantyra.org'],HasAdditionalSubjectAlternativeNames:kind==='truncated-SAN'};
  f.aws.read=async(side,service,command,input)=>{
    if(kind==='EC_prime256v1' && command==='SimulatePrincipalPolicy')introduced=true;
    if(side==='source' && service==='acm' && command==='ListCertificates'){
      inputs.push(input);const response=await read(side,service,command,input);
      if(introduced && (kind!=='EC_prime256v1'||input.Includes?.keyTypes?.includes('EC_prime256v1')))response.CertificateSummaryList.push(extra);
      return response;
    }
    if(side==='source' && service==='acm' && command==='DescribeCertificate' && input.CertificateArn===extra.CertificateArn)return {Certificate:{...extra,SubjectAlternativeNames:[...extra.SubjectAlternativeNameSummaries,'quantyra.org']}};
    return read(side,service,command,input);
  };
  if(kind==='www-primary'||kind==='truncated-SAN')introduced=true;
  const o=await new Collector({aws:f.aws,original,mapping}).observe({preflight:kind==='EC_prime256v1'});
  assert.ok(o.sourceCertificate);assert.ok(inputs.length>=2);assert.equal(introduced,true);
  record('R2-related-certificate-undisclosed-'+kind,{reproduced:true,extraCertificate:extra,extraActuallyExists:true,collectorReturnedSuccess:true,openingClosingInputs:inputs,fixtureMode:'Synthetic ACM applies documented key-type filtering; extra SAN Describe only if requested',fullSourceWrites:0});
});

test('R2 DNS absence helper marks default-key-filtered inventory complete',async()=>{
  let requested;const f=fakeAWS();
  const proof=await sourceCertificateAbsent({identify:f.aws.identify,read:async(side,service,command,input)=>{
    if(command==='DescribeCertificate'){const e=Error();e.name='ResourceNotFoundException';e.$metadata={requestId:'synthetic-old-absent',httpStatusCode:400};throw e;}
    requested=input;return {CertificateSummaryList:[],$metadata:{requestId:'synthetic-default-filtered'}};
  }});
  assert.equal(proof.inventory.complete,true);assert.equal(requested.Includes,undefined);
  record('R2-default-filtered-DNS-inventory-marked-complete',{reproduced:true,request:requested,proof});
});
