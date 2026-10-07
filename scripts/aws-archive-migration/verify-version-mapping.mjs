// Independent read-only all-version verification. --metadata-only is a quick
// inventory/header gate; the default also streams every destination byte.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import { STSClient,GetCallerIdentityCommand } from '@aws-sdk/client-sts';
import { fromIni } from '@aws-sdk/credential-providers';
import { SOURCE,DEST,defaults,inventory,hashBody,save } from './migrate.mjs';
import {sha} from './archive.mjs';
import {mappingCoverage,stableInventories} from './custody.mjs';
const cfg=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
const read=p=>fs.readFile(p,'utf8').then(JSON.parse),send=(c,n,a)=>c.send(new S3[n+'Command'](a));
const check=(ok,reason)=>{if(!ok){const e=Error();e.safeReason=reason;throw e;}};
export function sameHeaders(a,b) {
  for(const k of ['ContentType','ContentEncoding','ContentDisposition','CacheControl','ContentLanguage','WebsiteRedirectLocation'])if((a[k]??null)!==(b[k]??null))return false;
  if((a.Expires?.getTime()??null)!==(b.Expires?.getTime()??null))return false;
  const metadata=x=>JSON.stringify(Object.entries(x.Metadata||{}).sort());
  return metadata(a)===metadata(b);
}
export function sameTags(a,b){const tags=x=>JSON.stringify((x.TagSet||[]).map(t=>[t.Key,t.Value]).sort());return tags(a)===tags(b);}
async function main() {
  check(process.argv.length===2||process.argv.length===3&&process.argv[2]==='--metadata-only','unknown-verification-option');
  const metadataOnly=process.argv[2]==='--metadata-only',s=new S3.S3Client(cfg('cyint-ea-prod')),d=new S3.S3Client(cfg('quantyra'));
  for(const [p,a] of [['cyint-ea-prod','485386182336'],['quantyra','063280428495']])check((await new STSClient(cfg(p)).send(new GetCallerIdentityCommand({}))).Account===a,'wrong-account');
  const snapshot=await read(path.join(defaults.state,'source-versions.json')),mapping=await read(path.join(defaults.state,'version-mapping.json'));
  const live=await inventory(s,SOURCE,'485386182336'),destination=await inventory(d,DEST,'063280428495');
  const retained=await read(path.join(defaults.state,'repair/retained-versions.json')).catch(e=>{if(e.code==='ENOENT')return [];throw e;});
  mappingCoverage(live,mapping,destination,retained);
  check(JSON.stringify(live)===JSON.stringify(snapshot.rows),'source-inventory-changed');
  check(mapping.length===live.length&&mapping.every(m=>m.verified&&m.destination_version&&m.destination_version!=='null'),'incomplete-version-mapping');
  let verified=0,bytes=0;
  for(const row of live) {
    const m=mapping.find(x=>x.key===row.key&&x.version===row.version);
    check(m&&destination.some(x=>x.key===row.key&&x.version===m.destination_version&&x.kind===row.kind&&(!row.is_latest||x.is_latest)),'destination-version-visibility-mismatch');
    if(row.kind==='object') {
      const src={Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version},dst={Bucket:DEST,ExpectedBucketOwner:'063280428495',Key:row.key,VersionId:m.destination_version};
      const results=await Promise.allSettled([send(s,'HeadObject',src),send(d,'HeadObject',dst),send(s,'GetObjectTagging',src),send(d,'GetObjectTagging',dst)]);for(const r of results)if(r.status==='rejected')throw r.reason;
      const [sh,dh,st,dt]=results.map(r=>r.value);
      check(sh.ETag===row.etag&&sh.ContentLength===row.bytes&&dh.ContentLength===row.bytes&&dh.ServerSideEncryption==='AES256'&&sameHeaders(sh,dh)&&sameTags(st,dt),'object-header-or-tag-mismatch');
      if(!metadataOnly){const actual=await hashBody((await send(d,'GetObject',dst)).Body);check(actual.bytes===row.bytes&&actual.sha256===m.sha256,'destination-byte-hash-mismatch');bytes+=actual.bytes;}
    }
    verified++;if(verified%10===0||verified===live.length)console.log(JSON.stringify({verified_versions:verified,total:live.length,mode:metadataOnly?'metadata-only':'byte-hashes'}));
  }
  const endSource=await inventory(s,SOURCE,'485386182336'),endDestination=await inventory(d,DEST,'063280428495');stableInventories(live,endSource,destination,endDestination);
  const destinationFile=path.join(defaults.state,'repair/generic-verified-destination-inventory.json');await save(destinationFile,endDestination);
  await save(path.join(defaults.state,'repair',metadataOnly?'author-generic-metadata-verification.json':'author-generic-byte-verification.json'),{type:'archive-author-generic-verification-v1',independent_root_acceptance:false,at:new Date().toISOString(),metadata_only:metadataOnly,versions:verified,bytes,retained_versions:retained.length,source_stable:true,destination_stable:true,destination_coverage_complete:true,complete:true,source_inventory_sha256:sha(await fs.readFile(path.join(defaults.state,'source-versions.json'))),mapping_sha256:sha(await fs.readFile(path.join(defaults.state,'version-mapping.json'))),destination_inventory_sha256:sha(await fs.readFile(destinationFile)),code_sha256:sha(await fs.readFile(new URL('verify-version-mapping.mjs',import.meta.url)))});
}
if(process.argv[1]&&path.resolve(process.argv[1])===(await import('node:url')).fileURLToPath(import.meta.url))main().catch(e=>{console.error(JSON.stringify({status:'verification-failed',safe_reason:e.safeReason??null,error:e.name,http_status:e.$metadata?.httpStatusCode??null}));process.exitCode=1;});
