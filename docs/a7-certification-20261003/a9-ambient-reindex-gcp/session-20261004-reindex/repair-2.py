"""Routine repair of the two remaining second-run tactics and unused binders."""
from pathlib import Path
import difflib
p=Path(__file__).resolve().parent
repo=p.parents[3]
source=repo/'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean'
before=source.read_bytes()
(p/'repair-2-before.lean.snapshot').write_bytes(before)
s=before.decode('utf-8')
s=s.replace('    subst Y\n    rfl', '    change a9AmbientFinalMap A B A0 B0 X = Y at hInduces\n    subst Y\n    rfl')
s=s.replace('  intro z\n  rfl\n\n/-- Exact graph-factor', '  rintro ⟨A0, B0, X, hX, hA8A, hA8B⟩\n  rfl\n\n/-- Exact graph-factor')
s=s.replace('(∑ x : A9AmbientFixedFinalFiber', '(∑ _x : A9AmbientFixedFinalFiber')
assert s!=before.decode('utf-8')
source.write_bytes(s.encode('utf-8'))
(p/'repair-2.diff').write_text(''.join(difflib.unified_diff(before.decode('utf-8').splitlines(True),s.splitlines(True),fromfile='frozen-second-attempt',tofile='compiler-repair-2')),encoding='utf-8')
print('Exposed equality for subst; destructed sigma for definitional summand equality; marked unused sum binders. Statements unchanged.')
