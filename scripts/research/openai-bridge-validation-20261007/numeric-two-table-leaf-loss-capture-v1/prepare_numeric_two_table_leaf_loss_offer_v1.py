from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-two-table-leaf-loss-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'RobustSourceLineContainment',
                 'GrassmannCounting', 'GrassmannFlagPosterior']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
relative = 'numeric-transverse-agreement-loss-offer-20261011-v1/ActualTransverseAgreementLoss.lean'
expected = 'BCC8D7D4F5B71A4AC4A11CD00B5F0A7BB965628AFD63330A6519B968D09FFE74'
raw = (S / relative).read_bytes()
assert sha(raw) == expected
candidate_deps = [dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False)]
source = (OUT / 'ActualTwoTableLeafLoss.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['⊓', '≤', '→', '₁', '₂'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['transverseExceptionFraction_inf_window',
                   'transverseExceptionFraction_le_dimension_bound',
                   'agreement_ge_other_sub_two_exceptions',
                   'two_table_agreement_ge_sub_dyadic']
checks = 'import PvNP.RealizableHardness.ActualTwoTableLeafLoss\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualTwoTableLeafLoss.' + n + '\n'
                  for n in exports)
argument = '''# Two-table full-zoom leaf loss

E002/S3137. Complete argument precedes this translation in the planning numeric obligations note, section 2026-10-11 Two-table leaf loss and the posterior margin. This source is uncompiled and unaccepted.

Every leaf lies in the decoded window W, so intersecting H with W preserves its exact nontransversality event. The intersection has dimension at most that of H. The existing interval-transversality theorem then bounds its exception fraction by the reciprocal power with exponent dim(W)-j-d-1, with all subtraction and dimension guards explicit.

For two total tables equal on every leaf transverse to both spaces, the T1-agreement set is contained in the union of the T2-agreement set and both exceptional sets. Cardinality subadditivity and division by the same full zoom size give the additive agreement bound. Division by zero remains the zero-ratio convention, so no nonempty carrier hypothesis is required. Substituting both exception bounds gives twice the dyadic loss.

These four theorems prove the generic counting comparison. They do not supply the actual retained-space/table transport, its dimension guards, posterior tail/completion/rank exclusions, selected numeric margin, global strategy or source NO. Those remain the exact application steps recorded in the planning argument. Four parent interfaces match failed/unaccepted Full114 and the captured transverse-loss source has an exact dependency pin. No local Lean or Lake ran.

Remaining to-do list: authoritative kernel/axiom/warning verification, actual retained-table/posterior integration, legitimate decoder/source NO, common base/runtime, replay and all mandatory independent/final certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    data = path.read_bytes()
    assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in data.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(data), sha256=sha(data)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
