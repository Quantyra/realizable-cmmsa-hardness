"""Scoped Full118 proof-body repair; preserves the failed Full117 input. No Lean."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'full118-restricted-adjoint-repair-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full117-exact-real-complex-operators-repair7-resource02\input-archive.tar.gz')
PIN = '41BB9B0B971C39A85B49DB5D4FCC98445535242DBA0C13A4BEC5696124EDF3C4'
PACKET = S / 'full117-restricted-adjoint-diagnostic-packet-v2'
SOURCE = 'lean/PvNP/RealizableHardness/ExactRestrictedAdjoint.lean'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not OUT.exists(), 'Never overwrite offered or failed bytes'
assert sha(ARCHIVE.read_bytes()) == PIN
assert sha((PACKET / 'index.json').read_bytes()) == '8E9DFABB9C05A528AD3D23294A8F23479E6B3DB0832C0A1FAF538C9A5A0E9C39'
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    old = archive.extractfile(SOURCE).read()
    assert old == (PACKET / 'ExactRestrictedAdjoint.lean').read_bytes()
    assert sha(old) == '1BF81FA70064A4657FEBB0E82CC2C17C6901280BC24F1EB0CE0AFE7558137864'
    checks = archive.extractfile(SOURCE.replace('.lean', 'Checks.lean')).read()
    parent_manifest = json.load(archive.extractfile('capture-manifest.json'))
    dependencies = []
    for name in ['ExactAppendBlockIdentity', 'ExactAppendOperatorContracts',
                 'RectangularGLRowCompletion', 'RectangularGLSelectedRows',
                 'ActualFixedFunctionalAppendOperator', 'BinaryMatrixFourier']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'

new = old.decode('utf-8')
def replace_once(before, after):
    global new
    if '\r\n' in new:
        before = before.replace('\n', '\r\n')
        after = after.replace('\n', '\r\n')
    assert new.count(before) == 1, (before, new.count(before))
    new = new.replace(before, after)

replace_once('  let e := rightMulEquiv p', '  let e := rightMulEquiv (n := n) p')
replace_once('''    simpa [g, e, FirstBlock, appendBinaryMatrix] using
      (Equiv.sum_comp e (fun W : BinaryMatrix n (c + s) =>
        K W * H (FirstBlock W)))''', '''    calc
      (∑ p : BinaryMatrix n c × BinaryMatrix n s, g p.1 p.2) =
          ∑ p : BinaryMatrix n c × BinaryMatrix n s,
            K (e p) * H (FirstBlock (e p)) := by
              apply Finset.sum_congr rfl
              intro p _
              change K (appendBinaryMatrix p.1 p.2) * H p.1 =
                K (appendBinaryMatrix p.1 p.2) *
                  H (FirstBlock (appendBinaryMatrix p.1 p.2))
              rw [firstBlock_append]
      _ = _ := Equiv.sum_comp e (fun W : BinaryMatrix n (c + s) =>
        K W * H (FirstBlock W))''')
replace_once('''    rw [hsum, Fintype.card_prod]
    unfold BinaryMatrixFourier.uniformMean
    field_simp''', '''    have hcard : (Fintype.card (InversePair (c + s)) : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (InversePair (c + s)) ≠ 0)
    rw [hsum, Fintype.card_prod, Nat.cast_mul]
    unfold BinaryMatrixFourier.uniformMean
    exact mul_div_mul_left _ _ hcard''')

def headers(code):
    found = re.findall(r'(?ms)^(?:@\[[^\n]+\]\s*)?(?:theorem|def|abbrev)\s+\w+.*?(?=\s*:=)', code)
    return [re.sub(r'\s+', ' ', h) for h in found]
assert len(headers(new)) == 8
assert headers(old.decode()) == headers(new), 'Public statement drift'
assert re.findall(r'(?m)^import .*', old.decode()) == re.findall(r'(?m)^import .*', new)
assert re.findall(r'(?m)^set_option .*', old.decode()) == re.findall(r'(?m)^set_option .*', new)
assert not re.search(r'\b(?:sorry|admit|axiom)\b', new)
assert not new.startswith('\ufeff') and '\ufffd' not in new
assert all(glyph in new for glyph in ['∑', '→', '≃', '⟨', '≠'])
scope = dict(sources=len(parent_manifest['project_sources']),
             requests=len(parent_manifest['requested_axioms']), stages=len(parent_manifest['stages']))
assert scope == dict(sources=369, requests=347, stages=7)
OUT.mkdir()
(OUT / 'ExactRestrictedAdjoint.lean').write_bytes(new.encode('utf-8'))
(OUT / 'ExactRestrictedAdjointChecks.lean').write_bytes(checks)
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
argument = '''# Full118 restricted-adjoint repair

E002/S3137. Routine proof-body repair from the exact failed Full117 native input and complete immutable diagnostic packet. Full117 stages were 0/0/0/0/1/125/125 with 95 partial profiles. Its ExactAppendBlockIdentity repair passed; ExactRestrictedAdjoint then reported five module error headers (six including the aggregate failure), including two unsolved goals. All eight public headers, imports, options and original Checks are unchanged here. The complete failed source and logs remain immutable. No compiler runs in this preparation.

The three repairs preserve the same exact restricted-adjoint argument. First, rightMulEquiv has an ambient row dimension not determined by its inverse-pair argument; specify the already bound n. Second, identify the first block of the actual append bijection pointwise using the already proved firstBlock_append before applying Equiv.sum_comp. This avoids unfolding the append definition so far that simplification loses the applicable first-block theorem. The same full finite carrier and bijection are retained. Third, cast the product cardinality explicitly with Nat.cast_mul and cancel the inverse-pair cardinality by mul_div_mul_left. Its nonzero proof uses the identity inverse pair already present in the original proof. No matrix rank, extra invariance of H, additional independence, or source inequality is assumed.

No declaration, dependency, axiom request or resource guard is removed. Existing source line endings and mathematical glyphs are preserved, and UTF-8/no-BOM is checked. No warning is suppressed; the two pre-existing local-instance style warnings are left for the frozen warning comparison. The heartbeat cap is unchanged. Full118 must retain the complete 369-source, 347-request, seven-stage operator scope and all previous repairs. Numeric drafts are separate source-only work.

Remaining to-do list: immutable capture, full GCP source/Checks/fresh-axiom/no-regression verification and lifecycle custody; then all actual numeric/strategy/source-NO/runtime and mandatory independent/final certification gates.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / 'source.diff').write_text(''.join(difflib.unified_diff(old.decode().splitlines(True),
    new.splitlines(True), fromfile='Full117', tofile='Full118')), encoding='utf-8', newline='\n')
files = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
manifest = dict(schema=OUT.name, accepted=False, compiler_invoked=False,
    full117_input=dict(path=str(ARCHIVE), sha256=PIN), old_source_sha256=sha(old),
    new_source_sha256=sha(new.encode()), diagnostic_packet=str(PACKET),
    diagnostic_index_sha256=sha((PACKET / 'index.json').read_bytes()), dependencies=dependencies,
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_header_count=8,
    source_line_endings_preserved=True, parent_scope=scope, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new.encode()), checks_sha256=sha(checks),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), headers=8, parent_scope=scope)))
