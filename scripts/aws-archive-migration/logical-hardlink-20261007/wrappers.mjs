// Generator shared by future installation and isolated synthetic PS tests.
export function nodeWrapper(script) {
  return `import {spawn} from 'node:child_process';\nconst p=spawn(process.execPath,[${JSON.stringify(script)},...process.argv.slice(2)],{stdio:'inherit',windowsHide:true});\np.on('error',()=>{process.stderr.write('Restore entry unavailable\\n');process.exitCode=1;});\np.on('exit',c=>{process.exitCode=c??1;});\n`;
}
export function directoryWrapper() {
  return `param([Parameter(Mandatory=$true)][ValidateRange(1,44)][int]$DirectoryNumber,[ValidateSet('DryRun','VerifyOnly','Restore')][string]$Mode='DryRun',[string]$RelativeFile='',[switch]$Bounded)
$ErrorActionPreference='Stop'
$registry=Get-Content -LiteralPath "$env:USERPROFILE/.quantyra/aws-migration-20261006/active-restore-registry.json" -Raw|ConvertFrom-Json
if($registry.status-ne'verified-quantyra-archive-migration'){throw 'Missing verified archive registry'}
$entry=$registry.recovery|Where-Object{$_.directory-eq$DirectoryNumber}
if(@($entry).Count-ne1){throw 'Ambiguous directory catalog'}
if((Get-FileHash -LiteralPath $entry.catalog_file -Algorithm SHA256).Hash.ToLower()-ne$entry.catalog_sha256){throw 'Successor catalog hash mismatch'}
$commandArgs=@("$env:USERPROFILE/.local/bin/restore-quantyra-archive.mjs",'--catalog',$entry.catalog_file)
if($Mode-eq'DryRun'){$commandArgs+='--dry-run'}elseif($Mode-eq'VerifyOnly'){$commandArgs+='--verify-only'}else{
if($Bounded-and!$RelativeFile){throw 'Bounded restore needs one exact relative file'}
if(!$RelativeFile){$RelativeFile=$entry.selected_directory}
if($RelativeFile.EndsWith('/')){$RelativeFile=$RelativeFile.Substring(0,$RelativeFile.Length-1)}
if($RelativeFile.Contains('\\')-or$RelativeFile.Contains(':')-or@($RelativeFile.Split('/')|Where-Object{!$_-or$_-eq'.'-or$_-eq'..'}).Count){throw 'Unsafe relative file'}
if($RelativeFile-ne$entry.selected_directory-and!$RelativeFile.StartsWith($entry.selected_directory+'/',[StringComparison]::Ordinal)){throw 'File lies outside directory'}
$output=Join-Path $PSScriptRoot ('restore-quantyra-'+[guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $output|Out-Null
$commandArgs+=@('--workspace-root',$output,'--path',('realizable-cmmsa-hardness/'+$RelativeFile));if($Bounded){$commandArgs+='--bounded'}}
node @commandArgs
if($LASTEXITCODE){throw 'Archive operation failed; no launch clearance'}
Write-Output 'Restoration is not launch clearance; original frozen inputs and fresh prelaunch gates still apply.'
`;
}
