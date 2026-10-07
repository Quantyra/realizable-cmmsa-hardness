import https from 'node:https';
import { checkServerIdentity } from 'node:tls';
import { S3Client } from '@aws-sdk/client-s3';
import { STSClient, GetCallerIdentityCommand, AssumeRoleCommand, AssumeRoleWithWebIdentityCommand } from '@aws-sdk/client-sts';
import { fromIni } from '@aws-sdk/credential-providers';
import { NodeHttpHandler } from '@smithy/node-http-handler';
export const contract = Object.freeze({partition:'aws',region:'us-east-1',profile:'quantyra',account:'063280428495',principal_arn:'arn:aws:iam::063280428495:user/ServiceAdmin',s3_endpoint:'https://s3.us-east-1.amazonaws.com',sts_endpoint:'https://sts.us-east-1.amazonaws.com'});
export function validateContract(c) {
  if(JSON.stringify(c)!==JSON.stringify(contract)) throw Error('Official AWS contract required');
}
export function validateRequest(service, request) {
  const host=service==='s3'?'s3.us-east-1.amazonaws.com':'sts.us-east-1.amazonaws.com';
  if(!['s3','sts'].includes(service)||request.protocol!=='https:'||request.hostname!==host||request.port!=null&&request.port!==443||request.username||request.password) throw Error('Unofficial AWS request endpoint');
  const headers=request.headers??{};
  if(headers.host!==host || !/Credential=[^/]+\/\d{8}\/us-east-1\/(s3|sts)\/aws4_request/.test(headers.authorization??'') || !(headers.authorization??'').includes('/'+service+'/aws4_request')) throw Error('AWS signing scope mismatch');
}
// The final transport checks the serialized/signed request on every attempt.
// Explicit injection is for local SDK tests only; the CLI never supplies it.
export function officialClient(service, credentials, {testingTransport}={}) {
  const agent = new https.Agent({rejectUnauthorized:true,checkServerIdentity,minVersion:'TLSv1.2'});
  const real = testingTransport ?? new NodeHttpHandler({httpsAgent:agent,connectionTimeout:10000,requestTimeout:120000,throwOnRequestTimeout:true});
  const handler = {handle:async(r,o)=>{validateRequest(service,r);return real.handle(r,o);},destroy:()=>{real.destroy?.();agent.destroy();}};
  const config={region:contract.region,credentials,endpoint:service==='s3'?contract.s3_endpoint:contract.sts_endpoint,ignoreConfiguredEndpointUrls:true,useFipsEndpoint:false,useDualstackEndpoint:false,maxAttempts:3,requestHandler:handler};
  return service==='s3'?new S3Client({...config,forcePathStyle:true,useAccelerateEndpoint:false,followRegionRedirects:false}):new STSClient(config);
}
function profileCredentials() {
  // Explicit role assumers also cover STS calls made during profile resolution.
  const assume = Command => async (credentials,input) => {
    const client=officialClient('sts',credentials);
    try { const r=await client.send(new Command(input));if(!r.Credentials)throw Error('Missing assumed credentials');return {accessKeyId:r.Credentials.AccessKeyId,secretAccessKey:r.Credentials.SecretAccessKey,sessionToken:r.Credentials.SessionToken,expiration:r.Credentials.Expiration}; }
    finally {client.destroy();}
  };
  return fromIni({profile:contract.profile,roleAssumer:assume(AssumeRoleCommand),roleAssumerWithWebIdentity:assume(AssumeRoleWithWebIdentityCommand)});
}
export async function authenticatedReader(c, {testingCredentials,testingTransport}={}) {
  validateContract(c);
  // Resolve once: identity and S3 use exactly the same credential snapshot.
  const credentials=testingCredentials??await profileCredentials()();
  const sts=officialClient('sts',credentials,{testingTransport});let id;
  try {id=await sts.send(new GetCallerIdentityCommand({}));} finally {sts.destroy();}
  if(id.Account!==c.account || id.Arn!==c.principal_arn || !id.UserId)throw Error('Wrong AWS caller identity');
  const client=officialClient('s3',credentials,{testingTransport});
  return {client,identity:{account:id.Account,arn:id.Arn,partition:c.partition,region:c.region,s3_endpoint:c.s3_endpoint,sts_endpoint:c.sts_endpoint}};
}
