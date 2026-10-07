// Local byte checks only. No archive/client/key authentication or installation.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { defaults } from '../migrate.mjs';
import { sha } from '../archive.mjs';
import { requireThat as check } from '../custody.mjs';
import { here, repo, codeNames, committed } from './authorization.mjs';
async function main() {
  const args = process.argv.slice(2);
  check(args.length === 2 && args[0] === '--output', 'new-supplement-output-required');
  const git = promisify(execFile), commit = (await git('git',['rev-parse','HEAD'],{cwd:repo,windowsHide:true})).stdout.trim();
  const dirty = (await git('git',['status','--porcelain','--',path.relative(repo,here)],{cwd:repo,windowsHide:true})).stdout;
  check(!dirty.trim(), 'commit-successor-code-first');
  const packetBytes = await fs.readFile(path.join(defaults.state,'repair/fullscope-packet.json')), packet = JSON.parse(packetBytes);
  const oldCommit = '6bdf7532fb020397a5cf60c0bf7cc2afccb4cbac', acceptanceBytes = await committed(oldCommit,'archive-root-acceptance.json'), acceptance = JSON.parse(acceptanceBytes);
  check(sha(packetBytes) === acceptance.packet_sha256 && packet.artifacts.length === 305, 'old-accepted-packet-required');
  for (const p of packet.artifacts) check(sha(await fs.readFile(p.file)) === p.sha256, 'old-artifact-changed');
  for (const p of acceptance.catalogs) check(sha(await fs.readFile(p.catalog_file)) === p.catalog_sha256, 'catalog-changed');
  const code = [];
  for (const name of codeNames) {
    const file = path.join(here,name), gitPath = path.relative(repo,file).replaceAll('\\','/'), bytes = await fs.readFile(file);
    const blob = (await git('git',['show',commit+':'+gitPath],{cwd:repo,windowsHide:true,encoding:'buffer',maxBuffer:2*1024**2})).stdout;
    check(sha(blob) === sha(bytes), 'committed-code-bytes-required');code.push({file,git_path:gitPath,sha256:sha(bytes)});
  }
  const registry = await fs.readFile(path.join(defaults.state,'active-restore-registry.json'));
  const installation = await fs.readFile(path.join(defaults.state,'local-restore-installation.json'));
  const installed = JSON.parse(installation);
  for (const p of installed.active_tools) check(sha(await fs.readFile(p.file)) === p.sha256, 'installed-old-tool-changed');
  const supplement = {type:'archive-logical-hardlink-code-supplement-v1',at:new Date().toISOString(),code_commit:commit,old_root_acceptance_commit:oldCommit,old_root_acceptance_sha256:sha(acceptanceBytes),old_packet_sha256:sha(packetBytes),old_artifacts:packet.artifacts,catalogs:acceptance.catalogs,code_files:code,old_local_registry_sha256:sha(registry),old_local_installation_sha256:sha(installation),old_installed_tools:installed.active_tools,fresh_archive_authentication:false,data_versions_unchanged:true,installation_performed:false,claims:['Synthetic logical-hardlink, exact/prefix/multiple/full restoration, disk preflight and explicit bounded validation tests only; independent review and new root acceptance remain required.','Original 205 versions, 45 catalogs, authentication receipts, mappings and original packet remain byte-identical; no new live cryptographic proof.']};
  const bytes = Buffer.from(JSON.stringify(supplement,null,2)+'\n');
  await fs.writeFile(args[1],bytes,{flag:'wx',mode:0o600});
  console.log(JSON.stringify({type:supplement.type,sha256:sha(bytes),code_commit:commit,old_packet_pins:305,catalogs:45,fresh_authentication:false,installed:false}));
}
main().catch(e=>{console.error(JSON.stringify({status:'supplement-failed',safe_reason:e.safeReason??null,error:e.name}));process.exitCode=1;});
