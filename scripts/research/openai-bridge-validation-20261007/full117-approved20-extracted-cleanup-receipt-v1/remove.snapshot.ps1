param([Parameter(Mandatory=$true)][string]$TargetPath,[Parameter(Mandatory=$true)][string]$ExpectedSha,[Parameter(Mandatory=$true)][long]$ExpectedBytes)
$ErrorActionPreference = 'Stop'
$taskBase = [IO.Path]::GetFullPath('C:\Users\dfred\.quantyra\builder02')
$taskTarget = [IO.Path]::GetFullPath($TargetPath)
if (-not $taskTarget.StartsWith($taskBase + '\',[StringComparison]::OrdinalIgnoreCase)) { throw 'Outside bounded workspace' }
if ([IO.Path]::GetFileName($taskTarget) -ne 'package-sources.tar.gz') { throw 'Unexpected basename' }
$taskItem = Get-Item -LiteralPath $taskTarget -Force
if ($taskItem.PSIsContainer -or $taskItem.Length -ne $ExpectedBytes) { throw 'Wrong file identity' }
$taskInspect = $taskItem
while ($null -ne $taskInspect -and $taskInspect.FullName.StartsWith($taskBase,[StringComparison]::OrdinalIgnoreCase)) {
 if (($taskInspect.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) { throw 'Reparse path prohibited' }
 $taskInspect = $taskInspect.Parent
}
if ((Get-FileHash -LiteralPath $taskTarget -Algorithm SHA256).Hash -ne $ExpectedSha) { throw 'Changed target bytes' }
Remove-Item -LiteralPath $taskTarget -Force
if (Test-Path -LiteralPath $taskTarget) { throw 'Deletion did not finish' }
