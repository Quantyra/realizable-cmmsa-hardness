from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-visible-output-transport-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'ActualFiniteLaw',
                 'ActualStarAffineFunctionalSelection', 'SubmoduleFunctionalGluing',
                 'GrassmannCounting']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
relative = 'numeric-random-extension-offer-20261011-v1/ActualRandomExtensionSuccess.lean'
raw = (S / relative).read_bytes()
expected = '6FCB5FC2C7A00F24555287CCFCEAC98B754F277A8C4E3FE1FE830CD78FDB6D5B'
assert sha(raw) == expected
candidates = [dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False)]
relative = 'numeric-visible-list-strategy-offer-20261011-v1/ActualVisibleListStrategy.lean'
raw = (S / relative).read_bytes()
assert sha(raw) == '1E7176008530D5D0BB0DEE16C428A295FFD08E6CB7BFEC34F0BAFEE46DC85D77'
candidates.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualVisibleOutputTransport.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(chr(point) in code for point in [0x2211, 0x2200, 0x2264, 0x21a5])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
instances = re.findall(r'(?m)^noncomputable instance (\w+)', code)
assert exports == ['extensionMatchProbability_pushforward', 'transported_visible_strategy_match_lower',
                   'equivalent_visible_strategy_match_lower']
assert len(definitions) == 0 and len(instances) == 0
checks = 'import PvNP.RealizableHardness.ActualVisibleOutputTransport\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisibleOutputTransport.' + name + '\n'
                  for name in instances + definitions + exports)
plan = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning\docs\research\pvnp\full90-actual-rhs-numeric-no-obligations-2026-10-08.md')
planning = plan.read_text(encoding='utf-8')
heading = '## 2026-10-11 Output-law transport from the visible ambient'
assert planning.count(heading) == 1
argument = '# Visible output-law transport and exact-card matching cost\n\n'
argument += 'E002/S3137. UNCOMPILED and UNACCEPTED. Implements the output-law transport argument recorded before translation.\n\n'
argument += planning[planning.index(heading):] + '\n'
argument += ('The source proves exact finite pushforward matching and applies the actual ladder to the total visible strategy in a different equivalent ambient. The actual visible geometry, imported count, global game-law identity and source NO remain separate. All GCP and review gates remain open.\n')
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=candidates,
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, checked_instances=instances,
    imported_maximal_count_used=False, supplied_count_bound=False, actual_geometry_instantiated=False, derived_control=dict(path='prepare_numeric_visible_list_strategy_offer_v1.py', sha256='CB2AF88BBCC6CC85BDE8777BFE46B3E20DE0ADA18A429B1E62EA246D14E9A0FC'), files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports,
    checked_definitions=definitions, checked_instances=instances)))
