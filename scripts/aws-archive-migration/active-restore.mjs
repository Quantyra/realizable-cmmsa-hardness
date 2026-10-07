// Compatibility entry for protected local consumers. Historical inputs are
// redirected only through a verified, hash-pinned migration registry.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import { defaults,DEST,verifyCatalog } from './migrate.mjs';
import { sha,validate } from './archive.mjs';
import { restore } from './restore.mjs';
import { S3Client } from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import {decodeCatalog} from './catalog-bytes.mjs';
const o={},values={'--catalog':'catalog','--key-file':'keyFile','--workspace-root':'workspaceRoot','--profile':'profile'},flags={'--dry-run':'dryRun','--list':'list','--verify-only':'verifyOnly'};
async function main() {
  const a=process.argv.slice(2);for(let i=0;i<a.length;i++){if(values[a[i]]&&a[i+1]&&!a[i+1].startsWith('--'))o[values[a[i]]]=a[++i];else if(flags[a[i]])o[flags[a[i]]]=true;else if(a[i]==='--path'&&a[i+1]&&!a[i+1].startsWith('--'))(o.paths??=[]).push(a[++i]);else throw Error();}
  if(Object.keys(flags).filter(k=>o[flags[k]]).length>1)throw Error();
  const registry=JSON.parse(await fs.readFile(path.join(defaults.state,'active-restore-registry.json'),'utf8'));
  if(registry.status!=='verified-quantyra-archive-migration')throw Error();
  let catalog=o.catalog??registry.core.catalog_file;
  const input=await fs.readFile(catalog),fingerprint=sha(input);
  const entry=[registry.core,...registry.recovery].find(x=>x.source_catalog_sha256===fingerprint||x.catalog_sha256===fingerprint);
  if(!entry)throw Error();catalog=entry.catalog_file;
  const bytes=await fs.readFile(catalog);if(sha(bytes)!==entry.catalog_sha256)throw Error();
  const c=decodeCatalog(bytes);if(c.bucket!==DEST||c.profile!=='quantyra')throw Error();const {members}=validate(c);
  if(o.dryRun||o.list) {
    const selected=[...members.values()].filter(m=>!o.paths?.length||o.paths.some(p=>m.path===p.replace(/\/$/,'')||m.path.startsWith(p.replace(/\/$/,'')+'/')));
    if(!selected.length)throw Error();console.log(JSON.stringify({mode:o.list?'list':'dry-run',members:selected.length,bytes:selected.reduce((n,m)=>n+m.bytes,0),profile:'quantyra'}));return;
  }
  if(o.verifyOnly) {
    const client=new S3Client({region:'us-east-1',credentials:fromIni({profile:'quantyra'}),maxAttempts:3});
    const r=await verifyCatalog(client,c,o.keyFile??defaults.key,path.join(defaults.state,'consumer-verification-'+fingerprint.slice(0,16)),undefined,sha(bytes));
    console.log(JSON.stringify({mode:'verified',chunks:r.chunks.length,members:r.members}));return;
  }
  if(!o.workspaceRoot||o.paths?.length!==1)throw Error();
  console.log(JSON.stringify(await restore({catalog,keyFile:o.keyFile??defaults.key,workspaceRoot:o.workspaceRoot,path:o.paths[0]})));
}
main().catch(()=>{console.error('Protected Quantyra restore failed; bounded restore requires one exact regular member of at most 1 MiB. No payload printed.');process.exitCode=1;});
