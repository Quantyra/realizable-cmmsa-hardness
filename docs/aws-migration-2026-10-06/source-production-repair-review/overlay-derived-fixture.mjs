import fs from 'node:fs';import path from 'node:path';import os from 'node:os';import assert from 'node:assert/strict';import {spawnSync} from 'node:child_process';import {pins,hash} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';import {oldRecord} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/retirement-overlay.mjs';
function overlayFixture(){
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'website-overlay-fixture-'));
  const git=args=>{const x=spawnSync('git',args,{cwd:dir,encoding:'utf8'});assert.equal(x.status,0,x.stderr);return x.stdout.trim();};
  git(['init','-q']);git(['config','user.name','Synthetic Root']);git(['config','user.email','fixture@invalid']);
  const write=(name,value)=>{const bytes=Buffer.from(JSON.stringify(value));fs.writeFileSync(path.join(dir,name),bytes);return {path:name,sha256:hash(bytes)};};
  const proof=write('absence.json',{schema:1,kind:'SourceCertificateAbsent',certificateArn:pins.certificate,identity:{Account:pins.sourceAccount,Arn:pins.sourcePrincipal},describe:{error:'ResourceNotFoundException',requestId:'synthetic-describe',httpStatusCode:400},inventory:{complete:true,certificates:[],requestIds:['synthetic-list']},startedAt:1,completedAt:2});
  const disposition=write('disposition.json',{schema:1,owner:'root',accepted:true,certificateArn:pins.certificate,zone:pins.zone,record:oldRecord,retiredAt:3,sourceCertificateAbsent:proof});
  const review=write('review.json',{verdict:'GO',independent:true,reviewer:'independent',author:'author',toolingHash:'synthetic-reviewed-tooling'});
  git(['add','.']);git(['commit','-q','-m','Synthetic root evidence']);const evidenceCommit=git(['rev-parse','HEAD']);
  const gate=write('gate.json',{schema:1,enabled:true,phase:'dns',rootEvidenceCommit:evidenceCommit,rootAuthorization:{owner:'root',approved:true},resources:pins,review,toolingHash:'synthetic-reviewed-tooling',retirementOverlay:disposition});
  git(['add','gate.json']);git(['commit','-q','-m','Synthetic later root gate']);const gateCommit=git(['rev-parse','HEAD']);
  const control=write('control.json',{schema:1,enabled:true,rootRepository:dir,evidenceCommit,gateCommit,gate,disposition});
  git(['add','control.json']);git(['commit','-q','-m','Synthetic durable control']);
  return {dir,options:{repository:dir,controlPath:path.join(dir,'control.json')},git,write,control,cleanup:()=>fs.rmSync(dir,{recursive:true,force:true})};
}
export {overlayFixture};
