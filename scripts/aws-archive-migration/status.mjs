import * as S3 from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import { SOURCE, DEST, defaults } from './migrate.mjs';
import * as fs from 'node:fs/promises';
import path from 'node:path';
for(const profile of ['cyint-ea-prod','quantyra']) {
  const c=new S3.S3Client({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:1});
  for(const name of ['ListObjectVersions','ListMultipartUploads']) {
    const bucket=profile==='quantyra'?DEST:SOURCE;
    try {const r=await c.send(new S3[name+'Command']({Bucket:bucket,ExpectedBucketOwner:profile==='quantyra'?'063280428495':'485386182336',MaxKeys:1000,MaxUploads:1000}));console.log(JSON.stringify({profile,operation:name,objects:r.Versions?.length,markers:r.DeleteMarkers?.length,uploads:r.Uploads?.length,truncated:r.IsTruncated??false,status:'allowed'}));}
    catch(e){console.log(JSON.stringify({profile,operation:name,status:e.name,http:e.$metadata?.httpStatusCode??null}));}
  }
}
for(const name of ['source-versions.json','version-mapping.json','verify-source/verification-progress.json','verify-destination/verification-progress.json']) {
  const r=await fs.readFile(path.join(defaults.state,name),'utf8').then(JSON.parse).catch(()=>null);if(r)console.log(JSON.stringify({state:name,versions:r.rows?.length??(Array.isArray(r)?r.length:undefined),completed_chunks:r.completed?.length,max_catalog_bytes:r.rows?.filter(x=>x.key.endsWith('.json')).reduce((n,x)=>Math.max(n,x.bytes),0)}));
}
