// Author's read-only proof. Root independently reviews/runs its own acceptance.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import * as S3 from '@aws-sdk/client-s3';
import {fromIni} from '@aws-sdk/credential-providers';
import {SOURCE,DEST,defaults,inventory,save,preflight} from './migrate.mjs';
import {sha} from './archive.mjs';
import {decodeCatalog} from './catalog-bytes.mjs';
import {sameHeaders,sameTags} from './verify-version-mapping.mjs';
import {digest,requireThat as check,mappingCoverage,stableInventories,authenticatedCatalog} from './custody.mjs';
const read=p=>fs.readFile(p,'utf8').then(JSON.parse),base=path.join(defaults.state,'repair'),cfg=profile=>({region:'us-east-1',credentials:fromIni({profile}),maxAttempts:3});
async function main(){
  const s=new S3.S3Client(cfg('cyint-ea-prod')),d=new S3.S3Client(cfg('quantyra')),send=(c,n,a)=>c.send(new S3[n+'Command'](a));await preflight(d);
  const sourceFile=path.join(defaults.state,'source-versions.json'),mapFile=path.join(defaults.state,'version-mapping.json'),retainedFile=path.join(base,'retained-versions.json'),copyFile=path.join(base,'copy-all-receipt.json'),copy=await read(copyFile),mapping=await read(mapFile),retained=await read(retainedFile),snapshot=await read(sourceFile);
  check(copy.complete&&copy.versions===205&&copy.source_inventory_sha256===sha(await fs.readFile(sourceFile))&&copy.mapping_sha256===sha(await fs.readFile(mapFile))&&copy.retained_versions_sha256===sha(await fs.readFile(retainedFile)),'copy-terminal-bindings-mismatch');
  const source=await inventory(s,SOURCE,'485386182336'),destination=await inventory(d,DEST,'063280428495');check(digest(source)===digest(snapshot.rows),'source-snapshot-changed');mappingCoverage(source,mapping,destination,retained);
  // Authenticate catalog/member evidence, with all exact versions also bound to
  // the independently injective mapping. No repeat bulk reads of those versions.
  const coreFile=path.join(base,'core-successor.json'),catalogs=[{file:coreFile,proof:path.join(base,'core-authentication.json')}],discovery=await read(path.join(defaults.state,'recovery/discovery.json'));
  for(const x of discovery.catalogs){const n=Number(path.posix.basename(x.catalog_key).match(/directory-(\d\d)/)[1]);catalogs.push({file:path.join(defaults.state,'recovery/successor-catalogs',path.posix.basename(x.catalog_key)+'.gz'),proof:path.join(defaults.state,'recovery/verify-destination-'+n,'verification.json')});}
  check(catalogs.length===45,'full-catalog-set-required');const encrypted=new Set();
  for(const x of catalogs){const raw=await fs.readFile(x.file),c=decodeCatalog(raw),proof=await read(x.proof);authenticatedCatalog(c,sha(raw),proof);for(const ch of c.chunks){check(mapping.some(m=>m.key===ch.key&&m.destination_version===ch.version_id&&m.sha256===ch.sha256&&m.bytes===ch.bytes),'catalog-mapping-unbound');encrypted.add(JSON.stringify([ch.key,ch.version_id]));}}
  check(encrypted.size===105,'unique-encrypted-coverage-mismatch');let checked=0;
  for(const m of mapping){const src={Bucket:SOURCE,ExpectedBucketOwner:'485386182336',Key:m.key,VersionId:m.version},dst={Bucket:DEST,ExpectedBucketOwner:'063280428495',Key:m.key,VersionId:m.destination_version},[sh,dh,st,dt]=await Promise.all([send(s,'HeadObject',src),send(d,'HeadObject',dst),send(s,'GetObjectTagging',src),send(d,'GetObjectTagging',dst)]);check(sh.ETag===m.etag&&sh.ContentLength===m.bytes&&dh.ContentLength===m.bytes&&dh.ServerSideEncryption==='AES256'&&sameHeaders(sh,dh)&&sameTags(st,dt),'exact-version-metadata-mismatch');checked++;if(checked%25===0)console.log(JSON.stringify({author_metadata_versions:checked,total:205}));}
  const endSource=await inventory(s,SOURCE,'485386182336'),endDest=await inventory(d,DEST,'063280428495');stableInventories(source,endSource,destination,endDest);
  await save(path.join(base,'verified-source-inventory.json'),endSource);await save(path.join(base,'verified-destination-inventory.json'),endDest);
  await save(path.join(base,'author-version-verification.json'),{type:'archive-author-version-verification-v1',independent_root_acceptance:false,at:new Date().toISOString(),complete:true,versions:checked,destination_versions:endDest.length,retained_versions:retained.length,authenticated_unique_encrypted_versions:encrypted.size,opaque_hash_evidence:'bound-copy-terminal',bulk_hash_reuse:true,source_stable:true,destination_stable:true,source_inventory_sha256:sha(await fs.readFile(sourceFile)),mapping_sha256:sha(await fs.readFile(mapFile)),destination_inventory_sha256:sha(await fs.readFile(path.join(base,'verified-destination-inventory.json'))),copy_receipt_sha256:sha(await fs.readFile(copyFile)),code_sha256:sha(await fs.readFile(new URL('repair-verify.mjs',import.meta.url)))});
}
main().catch(e=>{console.error(JSON.stringify({status:'author-verification-failed',safe_reason:e.safeReason??null,error:e.name,http_status:e.$metadata?.httpStatusCode??null}));process.exitCode=1;});
