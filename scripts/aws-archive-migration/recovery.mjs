// Additional CMMSA recovery archives share the research key and bucket.
// Download only exact-version catalogs into protected custody; no raw payload
// or member names go to stdout or Git.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import { SOURCE, DEST, defaults, save, successor, verifyCatalog } from './migrate.mjs';
import { sha, validate } from './archive.mjs';
import { verifyCached } from './verification-cache.mjs';
import { authenticatedCatalog } from './custody.mjs';
import {decodeCatalog,saveCompressedCatalog} from './catalog-bytes.mjs';
const mode=process.argv[2],base=path.join(defaults.state,'recovery'),read=p=>fs.readFile(p,'utf8').then(JSON.parse);
const check=(ok,reason)=>{if(!ok){const e=Error();e.safeReason=reason;throw e;}};
const client=profile=>new S3.S3Client({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
async function main() {
  check(['discover','verify-source','verify-destination','activate'].includes(mode),'unknown-mode');
  const snapshot=await read(path.join(defaults.state,'source-versions.json')),s=client('cyint-ea-prod'),d=client('quantyra');
  const catalogs=snapshot.rows.filter(r=>r.kind==='object'&&r.is_latest&&/^migrations\/cmmsa44-recovery-20261007\/directory-\d\d-catalog\.json$/.test(r.key));
  check(catalogs.length===44&&new Set(catalogs.map(x=>x.key)).size===44,'incomplete-recovery-catalogs');const receipts=[],cache=new Map();
  const cacheFile=path.join(base,mode+'-immutable-cache.json');
  if(mode.startsWith('verify-')){const saved=await read(cacheFile).catch(e=>{if(e.code==='ENOENT')return null;throw e;});if(saved){check(saved.type==='immutable-chunk-authentication-cache-v1','unknown-cache-format');for(const [k,v] of saved.entries)cache.set(k,v);}}
  const mapping=mode==='discover'||mode==='verify-source'?[]:await read(path.join(defaults.state,'version-mapping.json'));
  for(const row of catalogs) {
    const name=path.posix.basename(row.key),file=path.join(base,'source-catalogs',name);
    if(mode==='discover') {
      check(row.bytes<=64*1024**2,'oversized-recovery-catalog');
      const r=await s.send(new S3.GetObjectCommand({Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:row.key,VersionId:row.version}));
      const parts=[];let bytes=0;for await(const b of r.Body){bytes+=b.length;check(bytes<=row.bytes,'catalog-size-exceeded');parts.push(b);}
      check(bytes===row.bytes,'catalog-size-mismatch');const data=Buffer.concat(parts),c=JSON.parse(data);validate(c);check(c.bucket===SOURCE,'recovery-bucket-mismatch');
      await fs.mkdir(path.dirname(file),{recursive:true});await fs.writeFile(file,data,{mode:0o600});
      receipts.push({catalog_key:row.key,version:row.version,catalog_sha256:sha(data),chunks:c.chunks.length,members:c.members.length,bytes:c.chunks.reduce((n,x)=>n+x.bytes,0)});
    } else {
      const original=await fs.readFile(file),c=JSON.parse(original),n=Number(name.match(/directory-(\d\d)/)[1]);
      const discovery=await read(path.join(base,'discovery.json')),pin=discovery.catalogs.find(x=>x.catalog_key===row.key&&x.version===row.version);
      check(pin?.catalog_sha256===sha(original),'recovery-catalog-changed');
      const next=mode==='verify-source'?c:successor(c,mapping,sha(original));
      if(mode==='activate') {
        const successorFile=path.join(base,'successor-catalogs',name+'.gz'),raw=await fs.readFile(successorFile),saved=decodeCatalog(raw);check(JSON.stringify(saved)===JSON.stringify(next),'recovery-successor-changed');const verified=await read(path.join(base,'verify-destination-'+n,'verification.json'));authenticatedCatalog(saved,sha(raw),verified);receipts.push({directory:n,members:c.members.length,activated:true,catalog_sha256:sha(raw),member_catalog_sha256:verified.member_catalog_sha256,verification_sha256:sha(await fs.readFile(path.join(base,'verify-destination-'+n,'verification.json')))});
      } else {
        const raw=mode==='verify-destination'?await saveCompressedCatalog(path.join(base,'successor-catalogs',name+'.gz'),next):original;
        const r=await verifyCached(mode==='verify-source'?s:d,next,defaults.key,path.join(base,mode+'-'+n),cache,cacheFile);r.catalog_sha256=mode==='verify-source'?sha(original):sha(raw);await save(path.join(base,mode+'-'+n,'verification.json'),r);
        receipts.push({directory:n,members:r.members,chunks:r.chunks.length,complete:r.complete,reused_chunks:r.reused_chunks,streamed_chunks:r.streamed_chunks});
      }
    }
    console.log(JSON.stringify({mode,completed_catalogs:receipts.length,total_catalogs:catalogs.length}));
  }
  const complete44=catalogs.length===44;const report={at:new Date().toISOString(),mode,catalogs:receipts,full_44_directory_set:complete44,complete:complete44};
  await save(path.join(base,mode==='discover'?'discovery.json':mode+'-receipt.json'),report);
  console.log(JSON.stringify({catalogs:receipts.length,members:receipts.reduce((n,x)=>n+x.members,0),complete:complete44}));
}
main().catch(async e=>{const failure={at:new Date().toISOString(),mode,error:e.name,safe_reason:e.safeReason??null,http_status:e.$metadata?.httpStatusCode??null};await save(path.join(base,mode+'-failure.json'),failure).catch(()=>{});console.error(JSON.stringify(failure));process.exitCode=1;});
