$ErrorActionPreference = 'Stop'
$base = Split-Path -Parent $MyInvocation.MyCommand.Path
$out = Join-Path $base 'local-three-sat-binary-codec-offer-20261012-v1'
$source = [IO.File]::ReadAllBytes((Join-Path $out 'LocalThreeSATBinaryCodec.lean'))
if ([Text.Encoding]::UTF8.GetString($source) -match '\bsorry\b|\badmit\b') { throw 'forbidden proof placeholder' }
$planning = 'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning'
$relative = 'docs/research/pvnp/openai-math-source-bridge-crosswalk-2026-10-06.md'
$heading = '## 2026-10-11 Input-language conversion without expanding sparse names'
$psi = [Diagnostics.ProcessStartInfo]::new()
$psi.FileName = 'git'
$psi.Arguments = '-C "' + $planning + '" show b4ff236:' + $relative
$psi.UseShellExecute = $false
$psi.RedirectStandardOutput = $true
$proc = [Diagnostics.Process]::Start($psi)
$memory = [IO.MemoryStream]::new()
$proc.StandardOutput.BaseStream.CopyTo($memory)
$proc.WaitForExit()
if ($proc.ExitCode -ne 0) { throw 'pinned git show failed' }
$blob = [Text.Encoding]::UTF8.GetString($memory.ToArray())
$section = $blob.Substring($blob.IndexOf($heading))
$next = $section.IndexOf("`n## ")
if ($next -ge 0) { $section = $section.Substring(0, $next) }
$argument = @'
# Codec argument and claim boundary

'@ + $section + @'

The scanner has finite states for zero, one, or two completed literals, a unary-name body, and the clause separator. A doubled sign pair emits the first-clause marker plus sign for the first literal, then only the sign for later literals. Each `11` name pair emits `[true,true]`; `01` emits a false name terminator; after literal three, `10` ends the clause without output. End of input emits `[false]` exactly between clauses. An odd suffix or illegal pair/state combination has no run result, and `convert` maps that failure to `[]`. The empty local formula maps to `[false]`, the target empty-formula encoding.

For exact-three formula phi, let c be its number of clauses and t the sum of its three variable indices per clause. The intended continuation lemma is `run between0 (phi.encode ++ tail) = (run between0 tail).map (fun suffix => emitFormula phi ++ suffix)`. It gives output `emitFormula phi`, with length `1 + 7*c + 2*t`; the local input length is `14*c + 2*t`. These are stated normal forms, not kernel-checked results in this offer.

The scanner success predicate must be identified with local `CNF.decode3?` success in both directions: `run between0 w != none` iff there exists phi with `CNF.decode3? w = some phi`. The forward direction recovers token blocks as the unique decoder output and shows exactly three literals per clause; the reverse direction unfolds the encoder and follows the matching scanner states. This includes malformed and odd-length words.

The local literal convention is `Lit.eval alpha ell = (alpha.get ell.var == ell.sign)`: true is positive, false is negated, and finite-list assignments default missing indices to false. Rename n to `g(n)=2^n-1`; its canonical binary digits are n true bits and g is injective by digit-list length. From local assignment alpha, extend by alpha on the image of g and false outside. Conversely, from upstream assignment beta, build a local list of length `maxVar(phi)+1` with nth entry `beta(g(n))`. Every variable in phi is below this finite bound. Literal truth and formula satisfaction are preserved both ways, including repeated literals and unused names.

The all-input endpoint still needs the actual upstream parser theorem: for every w, local `ThreeSAT.language w` iff `BinaryLanguage.language (convert w)`. On failed local parse, convert w is `[]`, which upstream must reject. On successful parse, prove exact parser round-trip on `emitFormula phi`, then apply the assignment correspondence. This offer does not claim that endpoint or FP membership. A concrete local TM, `ComputesInTime` witness, and polynomial clock remain separate work.

Argument pins: codec section b4ff236; finite assignment alignment ade0217; machine-model boundary c795dc1.

Remaining to-do list: prove continuation, decode3? equivalence, and length lemmas; connect the upstream parser for all inputs; construct a local TM with polynomial `ComputesInTime`; prove machine-model simulation. No Lean was run for this source-only offer.
'@
$utf8 = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $out 'ARGUMENT.md'), $argument, $utf8)
$checks = "import LocalThreeSATBinaryCodec`n`n#check LocalThreeSATBinaryCodecOffer.run`n#check LocalThreeSATBinaryCodecOffer.convert`n#check LocalThreeSATBinaryCodecOffer.convert_empty`n#check LocalThreeSATBinaryCodecOffer.emitFormula`n#print axioms LocalThreeSATBinaryCodecOffer.convert_empty`n"
[IO.File]::WriteAllText((Join-Path $out 'Checks.lean'), $checks, $utf8)
[IO.File]::WriteAllText((Join-Path $out '.gitattributes'), "* -text`n", [Text.Encoding]::ASCII)
$sha = [Security.Cryptography.SHA256]::Create()
function HashBytes([byte[]]$bytes) { return (($sha.ComputeHash($bytes) | ForEach-Object { $_.ToString('X2') }) -join '') }
$files = @()
Get-ChildItem -LiteralPath $out -File | Where-Object { $_.Name -ne 'manifest.json' } | Sort-Object Name | ForEach-Object {
  $bytes = [IO.File]::ReadAllBytes($_.FullName)
  $files += @{ path = $_.Name; bytes = $bytes.Length; sha256 = (HashBytes $bytes) }
}
$manifest = [ordered]@{
  schema = 'local-three-sat-binary-codec-offer-20261012-v1'
  story = 'E002/S3137'
  accepted = $false
  compiler_invoked = $false
  independent_static_review_completed = $false
  claim = 'source-only total scanner core and mathematical normal form; no endpoint or FP theorem'
  source_module = 'LocalThreeSATBinaryCodec'
  direct_imports = @('Complexitylib.SAT.Encoding')
  planning_argument_commit = 'b4ff236'
  related_argument_pins = @{ finite_assignment_alignment = 'ade0217'; machine_model_boundary = 'c795dc1' }
  dependencies = @(
    @{ path = 'Complexitylib/SAT/Encoding.lean'; revision = '6c248df7859f2f245e731c1e07057bf69d165fe2'; sha256 = '91F0850A60A73ACD9D59735E98022E90908E1DA92016D8B1B7E1ECF9F6D8F116' },
    @{ path = 'Complexitylib/SAT/ThreeSAT.lean'; revision = '6c248df7859f2f245e731c1e07057bf69d165fe2'; sha256 = '2AC675392479030D08EEFB9E289AB70B1D32C9F917E8D39AC4348B0AFC03FF86' },
    @{ path = 'Complexitylib/SAT/ThreeSAT/Syntax.lean'; revision = '6c248df7859f2f245e731c1e07057bf69d165fe2'; sha256 = '2EC65534D012DEB18C6872FC35D2D9CB298791282874007411E3FD8286B16BD7' }
  )
  verified_sign_convention = 'true positive, false negative; assignment List Bool getD false'
  semantic_endpoint_proved = $false
  fp_witness_proved = $false
  local_lean_run = $false
  files = $files
}
[IO.File]::WriteAllText((Join-Path $out 'manifest.json'), (($manifest | ConvertTo-Json -Depth 10) + "`n"), $utf8)
Get-ChildItem -LiteralPath $out -File | Sort-Object Name | ForEach-Object { '{0} {1}' -f $_.Name, (HashBytes ([IO.File]::ReadAllBytes($_.FullName))) }
