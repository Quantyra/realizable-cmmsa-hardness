"""Offline preparation of the bounded A9 reindex harness; no compiler execution."""
from pathlib import Path
import hashlib, json, shutil

repo = Path(__file__).resolve().parents[3]
old = repo / 'docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z'
pkg = Path(__file__).parent / 'session-20261004-reindex'
pkg.mkdir(exist_ok=False)
source = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean'
checks = source.replace('.lean', 'Checks.lean')
data = (repo/source).read_bytes()
(pkg/'source-before.lean.snapshot').write_bytes(data)
(pkg/'checks-before.lean.snapshot').write_bytes((repo/checks).read_bytes())
text = data.decode('utf-8')
text = text.replace('        a9AmbientA8Energy A B f Y := by\n  classical\n  rw [Finset.sum_const', '        (2 : Real) ^ (6 * D * k) * a9AmbientA8Energy A B f Y := by\n  classical\n  rw [Finset.sum_const')
text = text.replace('  have hreal := Nat.cast_le.mpr hmulR\n  have hprod := mul_le_mul_of_nonneg_right hreal hnonneg\n  push_cast at hprod ⊢\n  convert hprod using 1 <;> ring', '''  have hreal :
      (w6Gaussian a i * w6Gaussian b j *
        2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) : Nat) ≤
      (2 : Real) ^ (3 * D * (i + j + k)) := by
    exact_mod_cast hmulR
  have hprod := mul_le_mul_of_nonneg_right hreal
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _) hnonneg)
  simpa only [pow_add, mul_assoc] using hprod''')
assert text != data.decode('utf-8')
(repo/source).write_bytes(text.encode('utf-8'))
report = pkg.relative_to(repo).as_posix() + '/statement-fidelity.md'
(repo/report).write_text('''S3132 bounded analytic A9 actual-fiber reindexing/charge.

Before the first cloud build the exact theorem RHS was repaired to retain the
same 2^(6*D*k) graph factor as its LHS. The coarse proof multiplies the existing
multiplicity bound by the nonnegative graph factor and actual energy, retaining
the exponent 3*D*(i+j+k)+6*D*k. These are compiler/statement repairs only;
no new carrier, premise, weakened theorem or helper increment is authorized.
All hA/hB/hY/hi/hj remain explicit; the coarse theorem also retains hfin.
Three-lens reviews and full manuscript certification remain outstanding.
''', encoding='utf-8')
scripts = ['common.py','prepare.py','runner.py','audit.py','cloud_capture.py','validate.py','preserve-incomplete.py','remote-template.sh','README.md','.gitattributes','.gitignore']
for name in scripts:
    shutil.copyfile(old/name,pkg/name)
common = (pkg/'common.py').read_text(encoding='utf-8')
start = common.index('SOURCE = ')
end = common.index('STANDARD_AXIOMS = ')
frozen = {p: hashlib.sha256((repo/p).read_bytes()).hexdigest().upper() for p in [source,checks,report]}
common = common[:start] + f'SOURCE = {source!r}\nCHECKS = {checks!r}\nREPORT = {report!r}\nFROZEN = {frozen!r}\n' + common[end:]
common = common.replace('ActualBinaryMatrixHC46A9AmbientFiber.', 'ActualBinaryMatrixHC46A9AmbientReindex.')
common = common.replace("['a9AmbientFiberEquiv', 'a9Ambient_section_fiber_card', 'a9Ambient_extension_fiber_card', 'a9Ambient_nested_B0_card', 'a9_ambient_fiber_card']", "['a9AmbientA8PartitionEquiv', 'a9AmbientA8Energy_nonneg', 'a9Ambient_A8_sum_partition', 'a9Ambient_fixed_fiber_exact_charge', 'a9Ambient_fixed_fiber_coarse_charge']")
common = common.replace("CLAIM = 'Actual ambient", "CLAIM = 'Bounded analytic A9 partition and exact/coarse charge; prior ambient")
(pkg/'common.py').write_text(common,encoding='utf-8')
prepare = (pkg/'prepare.py').read_text(encoding='utf-8').replace('"PvNP.RealizableHardness.ActualBinaryMatrixHC46A9ActualFiber"', '"PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber"')
(pkg/'prepare.py').write_text(prepare,encoding='utf-8')
(pkg/'README.md').write_text('''# Bounded A9 actual-fiber reindex cloud evidence

Adapted from the retained prior A9 ambient immutable-capture runner.
All Lean execution is on the named GCP VM, guarded by metadata identity.
Each attempt has immutable input bytes, dependency custody, four compiler stages,
raw logs, legacy zero-total-warning audit and terminal receipt. Prospective
acceptance separately requires no new owned warnings and no baseline regression.
The 748 dependency and 13 prior ambient owned warning headers are S3137 debt.
No warning suppression, unrelated edits or three-lens reviews are authorized.
''',encoding='utf-8')
prior = old/'runs/cmmsa_a9_ambient_20261004T090505Z_189bd32b'
baseline = pkg/'warning-baseline'
baseline.mkdir()
for name in ['manifest.json.snapshot','audit.json','terminal.json']:
    shutil.copyfile(prior/name,baseline/name)
for i in range(4):
    for suffix in ['stdout','stderr','native-exit']:
        shutil.copyfile(prior/f'remote-evidence/stage-{i}.{suffix}',baseline/f'stage-{i}.{suffix}')
shutil.copyfile(repo.parent/'IGH/Quantyra-Planning/docs/local-codex-workflow-protocol.md',pkg/'workflow-protocol.snapshot')
print(pkg.relative_to(repo))
