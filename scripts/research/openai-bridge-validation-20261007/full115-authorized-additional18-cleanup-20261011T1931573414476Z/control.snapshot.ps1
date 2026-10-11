$ErrorActionPreference = 'Stop'
$repo = 'C:/Users/dfred/.quantyra/reviews/openai-bridge-validation-20261007'
$here = Join-Path $repo 'scripts/research/openai-bridge-validation-20261007'
$planPath = Join-Path $here 'full115-next-redundant-native-cleanup-plan-v1/plan.json'
$planPin = '7F5239118274572A666B753D7B3D57356D9636E378ACE06E2B90E860351BCF1F'
if ((Get-FileHash -LiteralPath $planPath).Hash -ne $planPin) { throw 'Frozen plan bytes changed' }
$plan = Get-Content -LiteralPath $planPath -Raw | ConvertFrom-Json
if ($plan.files.Count -ne 18 -or $plan.total_bytes -ne 714067101) { throw 'Exact approved scope changed' }
$base = (Resolve-Path -LiteralPath 'C:/a8gcp').Path
$retainedBase = (Resolve-Path -LiteralPath 'C:/Users/dfred/.quantyra/builder02').Path

function Assert-NoReparsePoint([string]$path) {
    $item = Get-Item -LiteralPath $path -Force
    while ($null -ne $item) {
        if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) { throw 'Reparse point forbidden' }
        if ($item -is [IO.FileInfo]) { $item = $item.Directory } else { $item = $item.Parent }
    }
}

$out = Join-Path $here ('full115-authorized-additional18-cleanup-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffffffZ'))
New-Item -ItemType Directory -Path $out | Out-Null
[IO.File]::WriteAllText((Join-Path $out '.gitattributes'), "* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol`n", [Text.UTF8Encoding]::new($false))
Copy-Item -LiteralPath $planPath -Destination (Join-Path $out 'approved-plan.json')
Copy-Item -LiteralPath $PSCommandPath -Destination (Join-Path $out 'control.snapshot.ps1')
$rows = @()
$before = (Get-PSDrive C).Free
$receiptPath = Join-Path $out 'receipt.json'
foreach ($row in $plan.files) {
    $target = (Resolve-Path -LiteralPath $row.remove).Path
    $retained = (Resolve-Path -LiteralPath $row.retain_original).Path
    if ([IO.Path]::GetDirectoryName($target) -ne $base -or $target -eq $retained) { throw 'Exact direct-parent containment failed' }
    if (-not $retained.StartsWith($retainedBase + '\', [StringComparison]::OrdinalIgnoreCase)) { throw 'Retained archive escapes named builder surface' }
    Assert-NoReparsePoint $target
    Assert-NoReparsePoint $retained
    if ((Get-Item -LiteralPath $target).Length -ne $row.bytes -or (Get-Item -LiteralPath $retained).Length -ne $row.bytes) { throw 'Paired size drift' }
    if ((Get-FileHash -LiteralPath $target).Hash -ne $row.sha256 -or (Get-FileHash -LiteralPath $retained).Hash -ne $row.sha256) { throw 'Paired SHA-256 drift' }
    Remove-Item -LiteralPath $target
    if (Test-Path -LiteralPath $target) { throw 'Exact approved short duplicate remains' }
    Assert-NoReparsePoint $retained
    if ((Get-Item -LiteralPath $retained).Length -ne $row.bytes -or (Get-FileHash -LiteralPath $retained).Hash -ne $row.sha256) { throw 'Retained original drift after deletion' }
    $rows += @{removed=$target; retained=$retained; bytes=$row.bytes; sha256=$row.sha256; utc=[DateTime]::UtcNow.ToString('o'); retained_verified_after=$true; no_reparse_points=$true}
    $receipt = @{authorization='Approve the additional 18 files'; authorization_received=$true; authorization_relay='Root relayed the explicit user reply to the exact pending 18-file question'; approved_plan_sha256=$planPin; only_exact_approved_files=$true; files_deleted=($rows.Count -eq 18); files=$rows; free_before=$before; free_after=(Get-PSDrive C).Free; complete_originals_retained=$true; compiler_invoked=$false; cloud_action=$false}
    [IO.File]::WriteAllText($receiptPath, (($receipt | ConvertTo-Json -Depth 8) + "`n"), [Text.UTF8Encoding]::new($false))
}
if ($rows.Count -ne 18) { throw 'Incomplete cleanup; retain exact partial receipt' }
Write-Output $out
Write-Output ('removed=' + $rows.Count)
Write-Output ('receipt_sha256=' + (Get-FileHash -LiteralPath $receiptPath).Hash)
Write-Output ('free_bytes=' + (Get-PSDrive C).Free)
