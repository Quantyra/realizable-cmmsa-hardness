import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';import path from 'node:path';import {fileURLToPath} from 'node:url';
import {overlayFixture} from './overlay-derived-fixture.mjs';import {harness} from './route-derived-harness.mjs';
import {pins,hash} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
import {loadOverlay,oldRecord,assertDesiredReplay,exactDeletePlan} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/retirement-overlay.mjs';
const results=[],here=path.dirname(fileURLToPath(import.meta.url));
test('Actual import/plan/stage bodies suppress old export, old desired plan and stale snapshots while preserving mail/destination validation',async()=>{
  const f=overlayFixture(),overlay=loadOverlay(f.options),old={Name:oldRecord.Name,Type:'CNAME',TTL:600,ResourceRecords:[{Value:oldRecord.Value}]};
  const mail={Name:'quantyra.org.',Type:'MX',TTL:600,ResourceRecords:[{Value:'10 mail.example.org.'}]},destination={Name:'_destination.quantyra.org.',Type:'CNAME',TTL:600,ResourceRecords:[{Value:'_new.acm-validations.aws.'}]};
  const original=JSON.stringify([old,mail,destination]),file=path.join(f.dir,'synthetic-export.json');fs.writeFileSync(file,original);const exportHash=hash(original);
  let actual=[old,mail,destination],writes=[];
  const h=harness({root:f.dir,config:{domains:pins.aliases},websiteLoad:()=>({certificate:pins.targetCertificate,distribution:pins.targetDistribution,domain:'d29u4d35k2uyay.cloudfront.net'}),clients:()=>({}),identity:async()=>({}),send:async()=>({Certificate:{Status:'ISSUED',DomainValidationOptions:[{ResourceRecord:{Name:destination.Name,Value:destination.ResourceRecords[0].Value}}]}}),loadOverlay:()=>loadOverlay(f.options),ownedZone:async()=>({id:pins.zone}),gate:async()=>{},listRecords:async()=>structuredClone(actual),route:async(command,input)=>{assert.equal(command,'ChangeResourceRecordSets');writes.push(input);for(const c of input.ChangeBatch.Changes){assert.notEqual(c.ResourceRecordSet.Name,oldRecord.Name);const r=c.ResourceRecordSet;actual=actual.filter(x=>x.Name!==r.Name||x.Type!==r.Type);actual.push(r);}return {ChangeInfo:{Id:'synthetic-route-change',Status:'PENDING'}};}});
  await h.importZone(file);assert.equal(hash(fs.readFileSync(file)),exportHash);assert.ok(h.load('source-export.json').records.some(r=>r.Name===oldRecord.Name));
  h.save('record-plan.json',{records:[old,mail,destination]});assert.throws(()=>assertDesiredReplay(h.load('record-plan.json').records,overlay),/ReplayBlocked/);
  h.save('staged-records.json',{records:[old,mail,destination]});await h.stage();
  assert.ok(writes.length>0);assert.ok(!h.load('record-plan.json').records.some(r=>r.Name===oldRecord.Name));assert.deepEqual(actual.find(r=>r.Type==='MX'),mail);assert.deepEqual(actual.find(r=>r.Name===destination.Name),destination);
  const proposal=exactDeletePlan(actual,overlay);assert.equal(proposal.enabled,false);assert.deepEqual(proposal.ChangeBatch.Changes,[{Action:'DELETE',ResourceRecordSet:old}]);
  actual=actual.map(r=>r.Name===oldRecord.Name?{...r,ResourceRecords:[{Value:'changed.example.org.'}]}:r);writes=[];await assert.rejects(h.stage(),/RetiredRecordChanged/);assert.equal(writes.length,0);
  results.push({name:'S3157-real-function-bodies-replay-suppression',passed:true,fixture:f.dir,exportSHA256:exportHash,overlay,disabledExactDelete:proposal,realCloudWrites:0,changedRetiredRecordPhysicalWrites:0});fs.writeFileSync(path.join(here,'independent-route-results.json'),JSON.stringify(results,null,2)+'\n');
});
