import * as fs from 'node:fs/promises';
import { constants } from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { fileURLToPath } from 'node:url';
import { defaults,DEST,save } from './migrate.mjs';
import { sha } from './archive.mjs';
const home=os.homedir(),here=path.dirname(fileURLToPath(import.meta.url)),read=p=>fs.readFile(p,'utf8').then(JSON.parse);
const check=(ok,reason)=>{if(!ok){const e=Error();e.safeReason=reason;throw e;}};
async function pinned(file) {const bytes=await fs.readFile(file);return {catalog_file:file,catalog_sha256:sha(bytes),catalog:JSON.parse(bytes)};}
async function backup(file) {
  const bytes=await fs.readFile(file),history=path.join(home,'.quantyra/migration-history/archive-aws-migration-20261006');await fs.mkdir(history,{recursive:true});
  const preserved=path.join(history,path.basename(file)+'.'+sha(bytes)+'.original');
  try{await fs.copyFile(file,preserved,constants.COPYFILE_EXCL);}catch(e){if(e.code!=='EEXIST')throw e;}
  check(sha(await fs.readFile(preserved))===sha(bytes),'local-tool-backup-mismatch');return {file,preserved,sha256:sha(bytes)};
}
async function main() {
  const coreFile=path.join(path.dirname(defaults.catalog),'research-archive-catalog.quantyra.json'),core=await pinned(coreFile),r=await read(path.join(defaults.state,'verify-destination/verification.json'));
  check(core.catalog.bucket===DEST&&r.complete&&r.members===core.catalog.members.length&&core.catalog.chunks.every(x=>r.chunks.some(y=>y.version_id===x.version_id&&y.ciphertext_sha256===x.sha256&&y.tar_sha256===x.tar_sha256)),'core-not-authenticated');
  const discovery=await read(path.join(defaults.state,'recovery/discovery.json')),activation=await read(path.join(defaults.state,'recovery/activate-receipt.json'));
  check(activation.complete&&activation.catalogs.length===44&&discovery.full_44_directory_set,'recovery-not-activated');
  const recovery=[];for(const x of discovery.catalogs){const file=path.join(defaults.state,'recovery/successor-catalogs',path.posix.basename(x.catalog_key)),p=await pinned(file),n=Number(path.posix.basename(file).match(/directory-(\d\d)/)[1]);check(p.catalog.bucket===DEST&&typeof p.catalog.selected_directory==='string','recovery-successor-account-mismatch');recovery.push({directory:n,catalog_file:file,catalog_sha256:p.catalog_sha256,source_catalog_sha256:x.catalog_sha256,selected_directory:p.catalog.selected_directory.replace(/^realizable-cmmsa-hardness\//,'')});}
  const registry={status:'verified-quantyra-archive-migration',core:{catalog_file:coreFile,catalog_sha256:core.catalog_sha256,source_catalog_sha256:sha(await fs.readFile(defaults.catalog))},recovery:recovery.sort((a,b)=>a.directory-b.directory)};
  await save(path.join(defaults.state,'active-restore-registry.json'),registry);
  const original=path.join(home,'.local/bin/restore-quantyra-archive.mjs'),history=await backup(original),script=path.join(here,'active-restore.mjs');
  const wrapper=`// Quantyra AWS migration active restore; historical tool retained in protected custody.\nimport {spawn} from 'node:child_process';\nconst child=spawn(process.execPath,[${JSON.stringify(script)},...process.argv.slice(2)],{stdio:'inherit',windowsHide:true});\nchild.on('error',()=>{process.stderr.write('Restore entry unavailable\\n');process.exitCode=1;});\nchild.on('exit',code=>{process.exitCode=code??1;});\n`;
  await fs.writeFile(original,wrapper,{mode:0o600});
  const recoveryTool=path.join(home,'.quantyra/recovery/cmmsa-44-20261007/restore-directory.ps1'),recoveryHistory=await backup(recoveryTool);
  // The registry provides exact successor hashes. Old raw catalogs and source
  // receipts remain unchanged; the active command requires no AWS CLI.
  const ps1=`param([Parameter(Mandatory=$true)][ValidateRange(1,44)][int]$DirectoryNumber,[ValidateSet('DryRun','VerifyOnly','Restore')][string]$Mode='DryRun',[string]$RelativeFile='')\n$ErrorActionPreference='Stop'\n$registry=Get-Content -LiteralPath "$env:USERPROFILE/.quantyra/aws-migration-20261006/active-restore-registry.json" -Raw|ConvertFrom-Json\nif($registry.status-ne'verified-quantyra-archive-migration'){throw 'Missing verified archive registry'}\n$entry=$registry.recovery|Where-Object{$_.directory-eq$DirectoryNumber}\nif(@($entry).Count-ne1){throw 'Ambiguous directory catalog'}\nif((Get-FileHash -LiteralPath $entry.catalog_file -Algorithm SHA256).Hash.ToLower()-ne$entry.catalog_sha256){throw 'Successor catalog hash mismatch'}\n$args=@("$env:USERPROFILE/.local/bin/restore-quantyra-archive.mjs",'--catalog',$entry.catalog_file)\nif($Mode-eq'DryRun'){$args+='--dry-run'}elseif($Mode-eq'VerifyOnly'){$args+='--verify-only'}else{if(!$RelativeFile){throw 'Bounded restore needs one exact relative file'};$filter='realizable-cmmsa-hardness/'+$RelativeFile;if(!$RelativeFile.StartsWith($entry.selected_directory+'/')){throw 'File lies outside directory'};$output=Join-Path $PSScriptRoot ('restore-quantyra-'+[guid]::NewGuid().ToString('N'));New-Item -ItemType Directory -Path $output|Out-Null;$args+=@('--workspace-root',$output,'--path',$filter)}\nnode @args\nif($LASTEXITCODE){throw 'Archive operation failed; no launch clearance'}\nWrite-Output 'Restoration is not launch clearance; original frozen inputs and fresh prelaunch gates still apply.'\n`;
  await fs.writeFile(recoveryTool,ps1,{mode:0o600});
  await save(path.join(defaults.state,'local-restore-installation.json'),{at:new Date().toISOString(),historical_tools:[history,recoveryHistory],active_tools:[{file:original,sha256:sha(Buffer.from(wrapper))},{file:recoveryTool,sha256:sha(Buffer.from(ps1))}],registry_sha256:sha(await fs.readFile(path.join(defaults.state,'active-restore-registry.json')))});
  console.log('Hash-pinned Quantyra restore consumers installed; historical tools preserved');
}
main().catch(e=>{console.error(JSON.stringify({status:'installation-failed',safe_reason:e.safeReason??null,error:e.name}));process.exitCode=1;});
