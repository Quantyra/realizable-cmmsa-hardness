import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import {Readable} from 'node:stream';
import {S3Client,GetObjectCommand} from '@aws-sdk/client-s3';
import {GetCallerIdentityCommand} from '@aws-sdk/client-sts';
import {officialClient,authenticatedReader,validateRequest,contract} from './aws-reader.mjs';
import {aliases,successorRegistry,authenticateRegistry,validateRegistryEvidence} from './registry.mjs';
import {sha} from '../../archive.mjs';
const credentials={accessKeyId:'AKID_SYNTHETIC',secretAccessKey:'SYNTHETIC_SECRET'};
const xml=(account=contract.account,arn=contract.principal_arn)=>'<GetCallerIdentityResponse xmlns="https://sts.amazonaws.com/doc/2011-06-15/"><GetCallerIdentityResult><Arn>'+arn+'</Arn><UserId>SYNTHETIC</UserId><Account>'+account+'</Account></GetCallerIdentityResult><ResponseMetadata><RequestId>synthetic</RequestId></ResponseMetadata></GetCallerIdentityResponse>';
const response=body=>({response:{statusCode:200,headers:{'content-type':'text/xml'},body:Readable.from([Buffer.from(body)])}});
const command=()=>new GetObjectCommand({Bucket:'quantyra-research-archive-063280428495-us-east-1',ExpectedBucketOwner:contract.account,Key:'synthetic',VersionId:'synthetic-version'});
for(const mode of ['defaults','global','service','profile','profile-services'])test('R1 official signed S3 and STS endpoints ignore '+mode+' overrides',async()=>{
 const dir=await fs.mkdtemp(path.join(os.tmpdir(),'qarc-endpoints-')),saved={};
 const vars=['AWS_ENDPOINT_URL','AWS_ENDPOINT_URL_S3','AWS_ENDPOINT_URL_STS','AWS_CONFIG_FILE','AWS_SHARED_CREDENTIALS_FILE','AWS_PROFILE','AWS_USE_FIPS_ENDPOINT','AWS_USE_DUALSTACK_ENDPOINT'];
 for(const k of vars){saved[k]=process.env[k];delete process.env[k];}
 try {
  const file=path.join(dir,'config');let text='[profile quantyra]\nregion = cn-north-1\n';
  if(mode==='global')process.env.AWS_ENDPOINT_URL='http://127.0.0.1:9';
  if(mode==='service'){process.env.AWS_ENDPOINT_URL_S3='https://unaccepted-s3.invalid';process.env.AWS_ENDPOINT_URL_STS='http://127.0.0.1:9';}
  if(mode==='profile')text+='endpoint_url = https://unaccepted-profile.invalid\n';
  if(mode==='profile-services')text+='services = custom\n[services custom]\ns3 =\n  endpoint_url = http://127.0.0.1:9\nsts =\n  endpoint_url = https://unaccepted-sts.invalid\n';
  await fs.writeFile(file,text);await fs.writeFile(path.join(dir,'credentials'),'');process.env.AWS_CONFIG_FILE=file;process.env.AWS_SHARED_CREDENTIALS_FILE=path.join(dir,'credentials');process.env.AWS_PROFILE='quantyra';process.env.AWS_USE_FIPS_ENDPOINT='true';process.env.AWS_USE_DUALSTACK_ENDPOINT='true';
  const seen=[],transport={handle:async r=>{seen.push(r);throw Error('LOCAL_STOP');}};
  for(const service of ['s3','sts']){const client=officialClient(service,credentials,{testingTransport:transport});try {await assert.rejects(client.send(service==='s3'?command():new GetCallerIdentityCommand({})),/LOCAL_STOP/);}finally{client.destroy();}}
  assert.equal(seen.length,2);for(const r of seen){assert.equal(r.protocol,'https:');assert.match(r.hostname,/^(s3|sts)\.us-east-1\.amazonaws\.com$/);assert.match(r.headers.authorization,/\/us-east-1\//);}
  assert.equal(seen[0].headers['x-amz-expected-bucket-owner'],contract.account);assert.equal(seen[0].query.versionId,'synthetic-version');
  // Reproduce the prior production constructor's unsafe resolution independently.
  if(mode!=='defaults'){let observed;const old=new S3Client({region:'us-east-1',credentials,useFipsEndpoint:false,useDualstackEndpoint:false,maxAttempts:1,requestHandler:{handle:async r=>{observed=r;throw Error('LOCAL_STOP');}}});try{await assert.rejects(old.send(command()),/LOCAL_STOP/);}finally{old.destroy();}assert(!observed.hostname.endsWith('.amazonaws.com'));}
 } finally {for(const k of vars){if(saved[k]===undefined)delete process.env[k];else process.env[k]=saved[k];}await fs.rm(dir,{recursive:true,force:true});}
});
test('R1 rejects unsigned, wrong-region, wrong-partition, TLS and hostile endpoint requests',()=>{
 const good={protocol:'https:',hostname:'s3.us-east-1.amazonaws.com',headers:{host:'s3.us-east-1.amazonaws.com',authorization:'AWS4-HMAC-SHA256 Credential=X/20261007/us-east-1/s3/aws4_request'}};
 assert.doesNotThrow(()=>validateRequest('s3',good));
 for(const change of [{protocol:'http:'},{hostname:'s3.cn-north-1.amazonaws.com.cn'},{hostname:'s3.us-east-1.amazonaws.com.evil.invalid'},{port:80},{headers:{...good.headers,host:'evil.invalid'}},{headers:{...good.headers,authorization:good.headers.authorization.replace('us-east-1','us-west-2')}},{headers:{...good.headers,authorization:''}}])assert.throws(()=>validateRequest('s3',{...good,...change}));
});
for(const mode of ['wrong-account','wrong-principal','failed-identity','correct'])test('R1 identity gate '+mode+' before any S3 request',async()=>{
 const calls=[],transport={handle:async r=>{calls.push(r);if(r.hostname.startsWith('sts')){if(mode==='failed-identity')throw Error('LOCAL_IDENTITY_FAIL');return response(xml(mode==='wrong-account'?'485386182336':contract.account,mode==='wrong-principal'?'arn:aws:iam::063280428495:user/Other':contract.principal_arn));}return response('synthetic-body');}};
 if(mode!=='correct'){await assert.rejects(authenticatedReader(contract,{testingCredentials:credentials,testingTransport:transport}));assert(calls.every(r=>r.hostname==='sts.us-east-1.amazonaws.com'));}
 else {const {client,identity}=await authenticatedReader(contract,{testingCredentials:credentials,testingTransport:transport});assert.equal(identity.account,contract.account);await client.send(command());client.destroy();assert.deepEqual(calls.map(r=>r.hostname),['sts.us-east-1.amazonaws.com','s3.us-east-1.amazonaws.com']);assert.equal(calls[0].headers.authorization.split('Credential=')[1].split('/')[0],calls[1].headers.authorization.split('Credential=')[1].split('/')[0]);}
});
function registryFixture(){
 const routes=Array.from({length:45},(_,i)=>({directory:i,catalog_file:'synthetic-'+i,catalog_sha256:sha(Buffer.from('catalog-'+i)),source_catalog_sha256:sha(Buffer.from('source-'+i)),selected_directory:'safe-'+i}));
 const old={status:'verified-quantyra-archive-migration',root_acceptance_commit:'a'.repeat(40),fullscope_packet_sha256:'b'.repeat(64),core:routes[0],recovery:routes.slice(1)};
 const bytes=JSON.stringify(old,null,2)+'\n',source=aliases(old),s={old_registry_utf8:bytes,old_local_registry_sha256:sha(Buffer.from(bytes)),old_root_acceptance_commit:old.root_acceptance_commit,old_packet_sha256:old.fullscope_packet_sha256,catalogs:routes.map((r,i)=>({directory:i,catalog_file:r.catalog_file,catalog_sha256:r.catalog_sha256})),source_aliases:source,source_aliases_sha256:sha(Buffer.from(JSON.stringify(source)))};
 return {supplement:s,rootCommit:'c'.repeat(40),supplementFile:'synthetic-supplement',supplementHash:'d'.repeat(64)};
}
test('R2 post-install aliases and ALL registry fields bind to accepted old bytes',()=>{
 const a=registryFixture(),installed=successorRegistry(a);authenticateRegistry(installed,a);
 const attacks=[r=>r.recovery[43].source_catalog_sha256=sha(Buffer.from('unaccepted-alias')),r=>r.core.source_catalog_sha256='0'.repeat(64),r=>r.recovery[3].catalog_file='other-file',r=>r.recovery[2].selected_directory='outside',r=>r.recovery.reverse(),r=>r.extra='unaccepted',r=>r.root_acceptance_commit='f'.repeat(40),r=>r.logical_hardlink_consumer.code_supplement_file='other-supplement',r=>r.fullscope_packet_sha256='0'.repeat(64),r=>r.status='stale'];
 for(const attack of attacks){const registry=structuredClone(installed);attack(registry);assert.throws(()=>authenticateRegistry(registry,a),/installed-registry-body-changed/);}
 const changed=structuredClone(a.supplement);changed.source_aliases[44].source_catalog_sha256='0'.repeat(64);assert.throws(()=>validateRegistryEvidence(changed));
 changed.old_registry_utf8+=' ';assert.throws(()=>validateRegistryEvidence(changed));
});
