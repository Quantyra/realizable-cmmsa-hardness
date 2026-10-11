"""Disjoint routine repair from the immutable Full116 native input. No Lean."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S/'full117-append-block-repair-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full116-exact-real-complex-operators-repair6-resource02\input-archive.tar.gz')
PIN = '242433DC6AC4E11ED509A1C5DE185AE05BFDD81850B558915A96026A49C57705'
PACKET = S/'full116-native-diagnostic-packet-v1'
SOURCE = 'lean/PvNP/RealizableHardness/ExactAppendBlockIdentity.lean'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not OUT.exists(), 'Never overwrite a source offer'
assert sha(ARCHIVE.read_bytes()) == PIN
assert sha((PACKET/'index.json').read_bytes()) == '2CDD36AB9A528366B0D0E29631B9FB903662F27D93518E090D3C9D60EC5FB48D'
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    old = archive.extractfile(SOURCE).read()
    assert old == (PACKET/'ExactAppendBlockIdentity.lean').read_bytes()
    assert sha(old) == '97076955CDB280238F18E511C1E66E5B64E1541E9CFE080561C98686CEFFC689'
    checks = archive.extractfile(SOURCE.replace('.lean', 'Checks.lean')).read()
    parent_manifest = json.load(archive.extractfile('capture-manifest.json'))
    dependencies = []
    for name in ['ExactAppendOperatorContracts', 'RectangularGLRowCompletion',
                 'RectangularGLSelectedRows', 'ActualFixedFunctionalAppendOperator',
                 'ActualAppendFourierCrossLevelOrthogonality']:
        member = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        raw = archive.extractfile(member).read()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
new = old.decode('utf-8')
def replace_once(before, after):
    global new
    # Preserve the original native CRLF source; normalize only replacement literals.
    if '\r\n' in new:
        before = before.replace('\n', '\r\n')
        after = after.replace('\n', '\r\n')
    assert new.count(before) == 1, (before, new.count(before))
    new = new.replace(before, after)
replace_once("    Matrix.transpose_mul, Matrix.mul_apply, LinearMap.toMatrix']",
             "    Matrix.transpose_mul, Matrix.mul_apply, LinearMap.toMatrix', Pi.single_apply]")
replace_once("    LastRows, Matrix.mul_apply, LinearMap.toMatrix']",
             "    RectangularGLSelectedRows.inversePairSwap,\n    LastRows, Matrix.mul_apply, LinearMap.toMatrix', Pi.single_apply]")
new, frame_count = re.subn(r'(?<!\.)\bFullRowFrame\b', 'ExactAppendOperatorContracts.FullRowFrame', new)
assert frame_count == 10, frame_count
replace_once('''  simp only [Matrix.mul_apply, Matrix.add_apply, FirstRows, LastRows,
    ActualAppendFourierCrossLevelOrthogonality.appendBinaryMatrix_apply_castAdd,
    ActualAppendFourierCrossLevelOrthogonality.appendBinaryMatrix_apply_natAdd]''',
    '''  simp only [Matrix.mul_apply, Matrix.add_apply, FirstRows, LastRows]''')
replace_once('      M = M * 1 := by simp',
             '      M = M * (1 : BinaryMatrix (c + s) (c + s)) := by simp')
replace_once('      rw [sub_mul, Matrix.mul_assoc]', '      rw [Matrix.sub_mul, Matrix.mul_assoc]')
replace_once('''  left_inv B := by ext i j <;> simp [sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]
  right_inv B := by ext i j <;> simp [sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]''', '''  left_inv B := sub_add_cancel B T
  right_inv B := add_sub_cancel_right B T''')
replace_once('''  have hA : (Fintype.card A : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hB : (Fintype.card B : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
''', '')
replace_once('''  rw [hsum, Fintype.card_prod, hsumDiv]
  field_simp''', '''  rw [hsum, Fintype.card_prod, Nat.cast_mul, hsumDiv, div_div]''')
replace_once('  letI : Nonempty (ExactAppendOperatorContracts.FullRowFrame s (c + s)) :=',
             '  haveI : Nonempty (ExactAppendOperatorContracts.FullRowFrame s (c + s)) :=')

def headers(code):
    found = re.findall(r'(?ms)^(?:theorem|def|abbrev)\s+\w+.*?(?=\s*:=)', code)
    return [re.sub(r'\s+', ' ', h).replace('ExactAppendOperatorContracts.FullRowFrame', 'FullRowFrame') for h in found]
assert headers(old.decode()) == headers(new), 'Public statement drift beyond explicit alias qualification'
assert re.findall(r'(?m)^import .*', old.decode()) == re.findall(r'(?m)^import .*', new)
assert re.findall(r'(?m)^set_option .*', old.decode()) == re.findall(r'(?m)^set_option .*', new)
assert not re.search(r'\b(?:sorry|admit|axiom)\b', new)
assert not '\ufffd' in new and not new.startswith('\ufeff')
OUT.mkdir()
(OUT/'ExactAppendBlockIdentity.lean').write_text(new, encoding='utf-8', newline='\n')
(OUT/'ExactAppendBlockIdentityChecks.lean').write_bytes(checks)
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
argument = '''# Full117 exact append/block repair

E002/S3137. Routine source-only repair against the exact Full116 input and complete native diagnostic packet. Full116 remains unaccepted. No compiler is run by this preparation, and all original declarations, mathematical hypotheses, imports, Checks and options are preserved. Ambiguous FullRowFrame names are explicitly qualified by the unchanged contract alias, whose underlying carrier is the identical surjective-matrix subtype.

Full116 compiled the repaired RectangularGLSelectedRows at stage4. ExactAppendBlockIdentity then failed on selector matrix entries, ambiguous aliases, an untyped identity, rectangular matrix distributivity, translation inverse simplification and product cardinality casting. The complete original source and native log remain immutable.

The first-column and inverse-bottom-row identities expand Pi.single entries so the finite sum selects exactly the requested coordinate. The bottom proof also unfolds the stored inverse-pair swap explicitly. The block decomposition and arbitrary rectangular matrices remain unchanged. Give M*1 its exact square matrix type; apply Matrix.sub_mul for the rectangular product rather than the scalar ring lemma. The append translation equivalence uses additive-group cancellation directly, so the two inverses do not depend on characteristic-two simplification. The normalized product mean casts the product cardinality explicitly and uses div_div, which is valid even without denominator nonzeroness; original Nonempty assumptions are retained unchanged.

Unused append selector simp arguments are removed where the original native log reported them, and the local Nonempty witness uses haveI. No warning is suppressed and no resource guard or heartbeat is changed. All original mathematical glyphs and UTF-8/no-BOM boundaries are checked. The only header differences are full qualification of the existing frame alias; the preparation normalizes that qualification and checks exact equality of every public header.

The repair still proves the original unrestricted-B pointwise identity and G-after-append equals Phi by exact uniform marginals; no rank conditioning, independence between GL marginals, new oracle or weakened target is introduced. Sol must capture these exact bytes and retain the complete369-source347-request seven-stage parent scope for GCP Full117.

Remaining to-do list: exact GCP kernel/axiom/no-regression checks, complete lifecycle custody, all numeric/decoder/source-NO/runtime and mandatory certification gates.
'''
(OUT/'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT/'source.diff').write_text(''.join(difflib.unified_diff(old.decode().splitlines(True), new.splitlines(True), fromfile='Full116', tofile='Full117')), encoding='utf-8', newline='\n')
files = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
manifest = dict(schema=OUT.name, accepted=False, compiler_invoked=False,
    full116_input=dict(path=str(ARCHIVE), sha256=PIN), old_source_sha256=sha(old), new_source_sha256=sha(new.encode()),
    diagnostic_packet=str(PACKET), diagnostic_index_sha256=sha((PACKET/'index.json').read_bytes()),
    dependencies=dependencies, mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_header_count=len(headers(new)), qualified_frame_occurrences=frame_count,
    prior_failed_control='prepare_full117_append_block_offer_v1.py',
    prior_failure='CRLF multiline replacement mismatch before any output directory was created',
    source_line_endings_preserved=True,
    parent_scope=dict(sources=len(parent_manifest['project_sources']), requests=len(parent_manifest['requested_axioms']), stages=len(parent_manifest['stages'])),
    files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new.encode()), checks_sha256=sha(checks),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), headers=len(headers(new))), indent=2))
