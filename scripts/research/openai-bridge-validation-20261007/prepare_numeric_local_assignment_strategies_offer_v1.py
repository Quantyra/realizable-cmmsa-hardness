"""Freeze the two actual local assignment laws and product identity; no Lean."""
from pathlib import Path
import hashlib, json, re, subprocess, sys, tarfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes

S = Path(__file__).resolve().parent
OUT = S/'numeric-local-assignment-strategies-offer-20261011-v1'
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    toolchain = archive.extractfile('lean-toolchain').read()
assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for module, directory, sourcepin, cappin in [
    ('ActualSharedAdviceSpans', 'numeric-shared-advice-spans-capture-v1',
     '51A0888A48FCC13A2DEE4B70477976F0DAE6FFA9417D3C46E993C0DE70F96A95',
     '11F2A0AAD2A13DC6EA04A25AEA4D4C3571AC469C1B3C269E5AFD6569DC4613A6'),
    ('ActualPrivateAssignmentLaw', 'numeric-private-assignment-law-capture-v1',
     'F69FA37EFC96F7ECE34660A585C64025BA9FF1E8826F8758AEEBCD5682AB875C',
     '438A9F32F7B2AE5C8B2E2D4EC5CB137BAA1E887EA0F0FBFAD790792245CC7871')]:
    capdir = S/directory
    index = (capdir/'index.json').read_bytes()
    assert sha(index) == cappin and sourcepin in index.decode()
    files = [p for p in capdir.glob('*.lean') if sha(p.read_bytes()) == sourcepin]
    assert len(files) == 1
    raw = files[0].read_bytes()
    candidates.append(dict(module='PvNP.RealizableHardness.'+module, path=str(files[0]),
        bytes=len(raw), sha256=sourcepin, capture_index=str(capdir/'index.json'),
        capture_sha256=cappin, accepted=False))
source = (OUT/'ActualLocalAssignmentStrategies.lean').read_bytes()
preflight = inspect_bytes(source, 'ActualLocalAssignmentStrategies.lean')
code = source.decode('utf-8')
imports = re.findall(r'(?m)^import (\S+)', code)
assert imports == [row['module'] for row in candidates]
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 4 and len(definitions) == 4
checks = 'import PvNP.RealizableHardness.ActualLocalAssignmentStrategies\n\n'
for name in definitions+exports:
    checks += '#check PvNP.RealizableHardness.ActualLocalAssignmentStrategies.'+name+'\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualLocalAssignmentStrategies.'+name+'\n'
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan = subprocess.run(['git', '-C', str(P), 'show', '3421337:'+relative], check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Actual local assignment strategies and their independent product'
text = plan.decode()
assert text.count(heading) == 1
section = text[text.index(heading):].split('\n## ', 1)[0]
argument = '# Actual local assignment strategies and literal product score\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n'+section+'\n'
for name, value in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT/name).write_text(value, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.rglob('*')):
    if path.is_file():
        raw = path.read_bytes()
        files.append(dict(path=path.relative_to(OUT).as_posix(), bytes=len(raw), sha256=sha(raw),
            diagnostic='diagnostics' in path.relative_to(OUT).parts))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, source_only_lexical_preflight=preflight, independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    candidate_dependencies=candidates, direct_imports=imports,
    planning_argument=dict(repository=str(P), relative_path=relative, committed_head='3421337',
        committed_blob_sha256=sha(plan), heading=heading, section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, local_strategy_laws_instantiated=True,
    first_strategy_has_no_draw_or_visible_question_argument=True,
    second_strategy_has_no_original_question_argument=True,
    normalized_fallbacks_present=True, independent_private_law_factorization_present=True,
    successful_prefix_score_identity_present=True, analysis_score_dominated=True,
    original_iid_row_law_composed=False, supplied_full_tuple_average_composed=False,
    ordered_row_eligibility_charged=False,
    source_game_law_identified=False, source_no_proved=False,
    supplied_final_probability_assumed=False, external_count_explicit_hypothesis=True,
    historical_dependency_pins_unchanged=True, dependency_successor_recompilation_required=True,
    files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), public_theorems=len(exports))))
