import * as fs from 'node:fs/promises';
import { constants } from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { sha } from '../../archive.mjs';
import { defaults } from '../../migrate.mjs';
import { requireThat as check } from '../../custody.mjs';
import { here, loadAuthorization } from './authorization.mjs';
import { successorRegistry } from './registry.mjs';
import { nodeWrapper, directoryWrapper } from './wrappers.mjs';
async function main() {
  const args = process.argv.slice(2);
  check(args.length === 2 && args[0] === '--root-acceptance-commit', 'new-root-commit-required');
  // All committed root/code/data gates run BEFORE creating any local output.
  const authorization = await loadAuthorization(args[1]), s = authorization.supplement;
  const registryFile = path.join(defaults.state,'active-restore-registry.json'), registryBytes = await fs.readFile(registryFile);
  check(sha(registryBytes) === s.old_local_registry_sha256, 'old-installed-registry-changed');
  check(sha(await fs.readFile(path.join(defaults.state,'local-restore-installation.json'))) === s.old_local_installation_sha256, 'old-installation-receipt-changed');
  for (const p of s.old_installed_tools) check(sha(await fs.readFile(p.file)) === p.sha256, 'old-installed-tool-changed');
  const home = os.homedir(), node = path.join(home,'.local/bin/restore-quantyra-archive.mjs'), ps = path.join(home,'.quantyra/recovery/cmmsa-44-20261007/restore-directory.ps1');
  check(s.old_installed_tools.length === 2 && [node,ps].every(file=>s.old_installed_tools.some(p=>path.resolve(p.file)===file)), 'installed-tool-set-mismatch');
  const registry = JSON.parse(registryBytes);
  check(registry.fullscope_packet_sha256 === s.old_packet_sha256 && registry.root_acceptance_commit === s.old_root_acceptance_commit, 'old-registry-acceptance-mismatch');
  const routes = [{...registry.core,directory:0},...registry.recovery];
  check(routes.length === 45 && s.catalogs.length === 45 && routes.every((e,i)=>e.directory===i&&s.catalogs.some(p=>p.directory===i&&p.catalog_file===e.catalog_file&&p.catalog_sha256===e.catalog_sha256)), 'old-catalog-routes-changed');
  const history = path.join(defaults.state,'logical-hardlink-installations',authorization.supplementHash);
  await fs.mkdir(history,{recursive:true});
  const preserved = [];
  for (const file of [registryFile,...s.old_installed_tools.map(p=>p.file)]) {
    const bytes = await fs.readFile(file), copy = path.join(history,path.basename(file)+'.'+sha(bytes)+'.original');
    try { await fs.copyFile(file,copy,constants.COPYFILE_EXCL); } catch(e) { if(e.code!=='EEXIST')throw e; }
    check(sha(await fs.readFile(copy))===sha(bytes),'history-backup-mismatch');preserved.push({file,preserved:copy,sha256:sha(bytes)});
  }
  const successor = successorRegistry(authorization);
  const active = [{file:node,bytes:Buffer.from(nodeWrapper(path.join(here,'active-restore.mjs')))},{file:ps,bytes:Buffer.from(directoryWrapper())},{file:registryFile,bytes:Buffer.from(JSON.stringify(successor,null,2)+'\n')}];
  for (const p of active) await fs.writeFile(p.file,p.bytes,{mode:0o600});
  const receipt = {at:new Date().toISOString(),root_acceptance_commit:args[1],code_supplement_sha256:authorization.supplementHash,preserved,active:active.map(p=>({file:p.file,sha256:sha(p.bytes)})),fresh_authentication:false};
  await fs.writeFile(path.join(history,'installation.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx',mode:0o600});
  console.log('Newly root-accepted logical restore consumers installed; old runtime/history retained');
}
main().catch(e=>{console.error(JSON.stringify({status:'installation-failed',safe_reason:e.safeReason??null,error:e.name}));process.exitCode=1;});
