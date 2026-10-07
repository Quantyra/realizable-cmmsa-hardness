import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import net from 'node:net';
import {fileURLToPath} from 'node:url';
import {fakeAWS,packetFixture} from './website-derived-fixture.mjs';
import {pins} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
import {loadPacket} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/packet.mjs';
import {adapterFor} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/lifecycle.mjs';
import {productionAWS} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/aws.mjs';
net.Socket.prototype.connect=function(){throw Error('REAL_SOCKET_FORBIDDEN');};
test('W2 refined: already resolved shared signer does not add a gate check at actual SDK transport',async()=>{
  const p=packetFixture();let now=Date.now(),mutations=0,expiredAtTransport=false,sourceCredentialResolutions=0;
  const packet=loadPacket({...p.options(),clock:()=>now});
  const aws=productionAWS({credentials:{source:async()=>{sourceCredentialResolutions++;return {accessKeyId:'SYNTHETIC_SOURCE',secretAccessKey:'SYNTHETIC'};},destination:{accessKeyId:'SYNTHETIC_DEST',secretAccessKey:'SYNTHETIC'}},requestHandler:{
    async handle(request){
      if(request.hostname.startsWith('sts.')){
        const source=String(request.headers.authorization).includes('SYNTHETIC_SOURCE');
        const account=source?pins.sourceAccount:pins.destinationAccount,arn=source?pins.sourcePrincipal:pins.destinationPrincipal;
        return {response:{statusCode:200,headers:{'content-type':'text/xml'},body:Buffer.from('<GetCallerIdentityResponse xmlns="https://sts.amazonaws.com/doc/2011-06-15/"><GetCallerIdentityResult><Account>'+account+'</Account><Arn>'+arn+'</Arn><UserId>SYNTHETIC</UserId></GetCallerIdentityResult><ResponseMetadata><RequestId>synthetic</RequestId></ResponseMetadata></GetCallerIdentityResponse>')}};
      }
      // Deterministic clock advance models signing/middleware/event-loop latency
      // between the last adapter verification and actual HTTP request dispatch.
      now=Date.parse(p.g.expiresAt)+1;mutations++;
      try{packet.verify();}catch(e){expiredAtTransport=/Expired|Stale/.test(e.message);}
      return {response:{statusCode:200,headers:{},body:Buffer.from('<UpdateDistributionResult/>')}};
    },destroy(){}}});
  try{
    await aws.identify();assert.equal(sourceCredentialResolutions,1);
    const f=fakeAWS();f.aws.mutateOnce=(...args)=>aws.mutateOnce(...args);
    const adapter=adapterFor(f.aws,packet),config=structuredClone(f.o.source.config);config.Aliases={Quantity:0};
    try{await adapter.mutateOnce('cloudfront','UpdateDistribution',{Id:pins.distribution,IfMatch:f.o.source.etag,DistributionConfig:config});}catch(e){assert.equal(mutations,1);}
    assert.equal(sourceCredentialResolutions,1);assert.equal(mutations,1);assert.equal(expiredAtTransport,true);
    const result={name:'W2-expiry-at-wire-with-warmed-shared-signer',reproduced:true,fixture:p.dir,sourceCredentialResolutions,physicalMutationRequests:mutations,expiredAtTransport,virtualClockInjection:'actual SDK transport handoff after final adapter verification',real_cloud_requests:0};
    fs.writeFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)),'independent-wire-expiry-results.json'),JSON.stringify(result,null,2)+'\n');
  }finally{aws.destroy();}
});
