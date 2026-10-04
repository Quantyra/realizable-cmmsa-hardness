"""Routine repairs from the preserved first GCP source diagnostics."""
from pathlib import Path
import difflib
p=Path(__file__).resolve().parent
repo=p.parents[3]
source=repo/'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean'
before=source.read_bytes()
(p/'repair-1-before.lean.snapshot').write_bytes(before)
s=before.decode('utf-8')
s=s.replace('open scoped BigOperators', 'open PvNP.RealizableHardness.BinaryMatrixFourier\nopen PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse\nopen scoped BigOperators')
s=s.replace('hpres.symm.trans hX', 'hpres.trans hX')
s=s.replace('  · rintro ⟨⟨Y, hY⟩, ⟨⟨A0, B0, X, hInduces⟩, hX⟩⟩\n    exact', '  · rcases z with ⟨⟨Y, hY⟩, ⟨⟨A0, B0, X, hInduces⟩, hX⟩⟩\n    exact')
start=s.index('  · intro z\n    rcases z with ⟨A0, B0, X, hX, hA8A, hA8B⟩')
end=s.index('\nprivate def a9AmbientA8Energy', start)
s=s[:start]+'''  · rintro ⟨A0, B0, X, hX, hA8A, hA8B⟩
    rfl
  · rintro ⟨⟨Y, hY⟩, ⟨⟨A0, B0, X, hInduces⟩, hX⟩⟩
    subst Y
    rfl
'''+s[end:]
start=s.index('  let p := a9AmbientA8PartitionEquiv')
end=s.index('\n/-- Exact graph-factor',start)
s=s[:start]+'  rfl\n'+s[end:]
s=s.replace('    intro T hT', '    intro T _hT')
s=s.replace('(pow_nonneg (by norm_num : (0 : Real) ≤ 2) _) hnonneg)', '(pow_nonneg (by norm_num : (0 : Real) ≤ 2) (6 * D * k)) hnonneg)')
source.write_bytes(s.encode('utf-8'))
(p/'repair-1.diff').write_text(''.join(difflib.unified_diff(before.decode('utf-8').splitlines(True),s.splitlines(True),fromfile='frozen-first-attempt',tofile='compiler-repair-1')),encoding='utf-8')
print('Repaired rank equality, argument destructuring, inverse laws, namespace resolution and definitional sum equality; no signature changes.')
