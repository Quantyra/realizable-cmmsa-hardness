import * as fs from 'node:fs/promises';
import path from 'node:path';
import { S3Client } from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import { defaults, DEST, verifyCatalog } from '../migrate.mjs';
import { sha, validate } from '../archive.mjs';
import { decodeCatalog } from '../catalog-bytes.mjs';
import { loadAuthorization, authorizeRoute } from './authorization.mjs';
import { restore, plan } from './restore.mjs';
async function main() {
  const o = {paths:[]}, values = {'--catalog':'catalog','--key-file':'keyFile','--workspace-root':'workspaceRoot','--profile':'profile'}, flags = {'--dry-run':'dryRun','--list':'list','--verify-only':'verifyOnly','--bounded':'bounded'};
  const args = process.argv.slice(2);
  for (let i = 0; i < args.length; i++) {
    if(args[i]==='--path'&&args[i+1]&&!args[i+1].startsWith('--'))o.paths.push(args[++i]);
    else if (values[args[i]] && args[i+1] && !args[i+1].startsWith('--') && o[values[args[i]]] == null) o[values[args[i]]] = args[++i];
    else if (flags[args[i]]) o[flags[args[i]]] = true;
    else throw Error('Invalid options');
  }
  if (['dryRun','list','verifyOnly'].filter(k => o[k]).length > 1 || o.bounded && o.verifyOnly) throw Error('Conflicting modes');
  const registry = JSON.parse(await fs.readFile(path.join(defaults.state,'active-restore-registry.json'),'utf8'));
  if (registry.status !== 'verified-quantyra-archive-migration' || !registry.logical_hardlink_consumer) throw Error('New accepted installation required');
  const binding = registry.logical_hardlink_consumer;
  const authorized = await loadAuthorization(binding.root_acceptance_commit, binding.code_supplement_file);
  if (authorized.supplementHash !== binding.code_supplement_sha256 || registry.fullscope_packet_sha256 !== authorized.supplement.old_packet_sha256) throw Error('Consumer authorization mismatch');
  const input = await fs.readFile(o.catalog ?? registry.core.catalog_file), fingerprint = sha(input);
  const entry = [registry.core,...registry.recovery].find(x => x.catalog_sha256 === fingerprint || x.source_catalog_sha256 === fingerprint);
  if (!entry) throw Error('Unregistered catalog');
  const bytes = await fs.readFile(entry.catalog_file), pin = authorized.supplement.catalogs.find(x => x.catalog_file === entry.catalog_file);
  if (!pin || sha(bytes) !== entry.catalog_sha256 || pin.catalog_sha256 !== entry.catalog_sha256) throw Error('Catalog pin mismatch');
  const c = decodeCatalog(bytes), {members} = validate(c);
  if (c.bucket !== DEST || c.profile !== 'quantyra') throw Error('Wrong account');
  if(pin.directory>0&&!o.paths.length)o.paths=[c.selected_directory.replace(/\/$/,'')];
  authorizeRoute(pin,entry,c,o.paths,entry===registry.core);
  if (o.dryRun || o.list) {
    const p=plan(c,o.paths,{bounded:o.bounded??false});
    console.log(JSON.stringify({mode:o.list?'list':'dry-run',members:p.outputs.length,bytes:p.bytes,required_disk_bytes:String(p.requiredDiskBytes),profile:'quantyra'}));return;
  }
  if(!o.verifyOnly&&!o.workspaceRoot)throw Error('Separate output workspace required');
  const client = new S3Client({region:'us-east-1',credentials:fromIni({profile:'quantyra'}),maxAttempts:3});
  if (o.verifyOnly) { const r = await verifyCatalog(client,c,o.keyFile??defaults.key,path.join(defaults.state,'logical-consumer-verification-'+fingerprint.slice(0,16)),undefined,sha(bytes));console.log(JSON.stringify({mode:'verified',chunks:r.chunks.length,members:r.members}));return; }
  console.log(JSON.stringify(await restore({catalog:entry.catalog_file,keyFile:o.keyFile??defaults.key,workspaceRoot:o.workspaceRoot,paths:o.paths,bounded:o.bounded??false},client)));
}
main().catch(()=>{console.error('Accepted bounded logical restore failed; no payload printed.');process.exitCode=1;});
