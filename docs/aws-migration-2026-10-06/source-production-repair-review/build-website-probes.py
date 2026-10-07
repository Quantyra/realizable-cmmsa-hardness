import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
WEB=REPO.parent/'Quantyra-Website'
SOURCE=WEB/'scripts/aws-migration/source-lifecycle/integration.test.mjs'
code=SOURCE.read_text().split("\ntest(",1)[0]
def replace(m):return "from '"+(SOURCE.parent/m.group(1)).resolve().as_uri()+"'"
code=re.sub(r"from '(\.[^']+)'",replace,code)
code+='\nexport {fakeAWS,packetFixture,captured,original,mapping};\n'
(HERE/'website-derived-fixture.mjs').write_text(code,encoding='utf-8')
original=REPO/'docs/aws-migration-2026-10-06/source-lifecycle-review/independent-website.test.mjs'
test=original.read_text()
test=test.replace("real packet loader accepts wholly uncommitted evidence/gate fixtures","real packet loader rejects missing committed Root provenance")
start=test.index("  const p=packetFixture(), packet=loadPacket(p.options());packet.verify();")
end=test.index("\n});",start)
test=test[:start]+"  const p=packetFixture();const options=p.options();assert.throws(()=>loadPacket({...options,evidenceCommit:undefined,gateCommit:undefined}),/SeparateRootCommitsRequired/);record('W1-uncommitted-packet-rejected',{passed:true,fixture:p.dir});"+test[end:]
test=test.replace("expiry during real SDK credential resolution still reaches physical mutation","expiry during real SDK credential resolution blocks physical mutation")
test=test.replace("catch(e){assert.equal(sends,1);}","catch(e){assert.match(e.message,/Expired|Stale/);assert.equal(sends,0);}")
test=test.replace("assert.equal(sends,1);assert.equal(atWireExpired,true);","assert.equal(sends,0);assert.equal(expired(packet),true);")
test=test.replace("record('W2-expired-at-physical-send',{reproduced:true","record('W2-expired-at-physical-send-rejected',{passed:true")
test=test.replace("retirement kernel returns observed after gate expires during final journal fsync","retirement kernel rejects success after final journal fsync expiry")
test=test.replace("  const state=await runner.run('retire','certificate');\n  assert.equal(state,'observed');assert.equal(expired(packet),true);assert.equal(mutations,1);", "  await assert.rejects(runner.run('retire','certificate'),/Expired|Stale/);const state=journal.read().at(-1).state;assert.equal(state,'observed');assert.equal(expired(packet),true);assert.equal(mutations,1);")
test=test.replace("record('W3-success-returned-after-terminal-expiry',{reproduced:true","record('W3-terminal-expiry-success-rejected',{passed:true")
test=test.replace("collector misses source ","collector rejects source ")
test=test.replace("  const o=await collector.observe({step:'certificate'});\n  assert.equal(recreated,true);assert.equal(resource==='bucket'?o.bucketAbsent:o.certificateAbsent,true);", "  await assert.rejects(collector.observe({step:'certificate'}),/ChangedAfterDependencySweep/);assert.equal(recreated,true);")
test=test.replace("record('W4-stale-source-'+resource+'-absence',{reproduced:true","record('W4-source-'+resource+'-recreation-rejected',{passed:true")
test=test.replace("  const r=await simulate(aws,'DeleteObject',resource,null,[{ContextKeyName:'s3:VersionId',ContextKeyType:'string',ContextKeyValues:['null']}]);\n  assert.equal(r.decision,'allowed');record('W5-denied-resource-result-accepted',{reproduced:true,returned:r});", "  await assert.rejects(simulate(aws,'s3:DeleteObjectVersion',resource,null,[{ContextKeyName:'s3:VersionId',ContextKeyType:'string',ContextKeyValues:['null']}]),/ResourceDeniedOrInconsistent/);record('W5-denied-resource-result-rejected',{passed:true});")
start=test.index("test('W6:")
end=test.index("\ntest('negative control",start)
test=test[:start]+"""test('W6: never-versioned compiler permits both known cleanup actions and simulates both with exact principal/resource and no VersionId',async()=>{
  assert.deepEqual(captured.baseline.bucketControls.GetBucketVersioning,{});
  const policy=freezePolicy(captured.baseline.originalBucketPolicy,original),deny=policy.Statement.find(s=>s.Sid==='LifecycleDenyAllNonReadExceptKnownCleanup');
  assert.ok(deny.NotAction.includes('s3:DeleteObject'));assert.ok(deny.NotAction.includes('s3:DeleteObjectVersion'));assert.ok(!deny.NotAction.includes('s3:PutObject'));
  const sent=[],resource='arn:aws:s3:::'+pins.bucket+'/'+original[0].key;
  const aws={read:async(s,v,c,i)=>{sent.push(i);return {IsTruncated:false,EvaluationResults:[{EvalActionName:i.ActionNames[0],EvalResourceName:resource,EvalDecision:'allowed',ResourceSpecificResults:[{EvalResourceName:resource,EvalResourceDecision:'allowed'}]}]};}};
  const {simulateDelete}=await import('file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/collector.mjs');
  await simulateDelete(aws,resource,policy);
  assert.deepEqual(sent.map(s=>s.ActionNames[0]),['s3:DeleteObject','s3:DeleteObjectVersion']);
  assert.ok(sent.every(s=>s.CallerArn===pins.sourcePrincipal && s.PolicySourceArn===pins.sourcePrincipal && s.ResourceArns[0]===resource && !s.ContextEntries.some(c=>c.ContextKeyName==='s3:VersionId')));
  record('W6-unversioned-contract-repaired',{passed:true,requests:sent,liveDeletionAttempted:false});
});
"""+test[end:]
(HERE/'independent-website-adapted.test.mjs').write_text(test,encoding='utf-8')
(HERE/'probe-provenance.json').write_text(json.dumps({'fixture_source':str(SOURCE),'fixture_source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'fixture_method':'Extract current owner fixture prefix before first test; rebind relative imports to actual production modules. No production code changes.','retained_probe_source':str(original),'retained_probe_source_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),'adaptation':'Reverse original defect expectations to refusal; W1 omit committed provenance; W5 retain actual IAM action; W6 use repaired dual-permission contract. Retain originals unchanged.'},indent=2)+'\n')
