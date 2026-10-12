from pathlib import Path
import hashlib, json, re, subprocess, tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-private-assignment-law-offer-20261011-v1'
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
inventory_path = S / 'complete-numeric-source-only-inventory-v15.json'
inventory_raw = inventory_path.read_bytes()
assert sha(inventory_raw) == 'DF4888CA1D5AFB8280F6CAE4DFB7ACA5848DAD9578A3B0D221A2300FEC101A6A'
inventory = json.loads(inventory_raw)
routes = {row['path']: row for row in inventory['selected_sources']}
source = (OUT / 'ActualPrivateAssignmentLaw.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert all(x not in code for x in ['\ufffd', '\u00e2\u02c6', '\u00e2\u2020', '\\sum', '\\r\\n'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
stack, depth, quoted, i = [], 0, False, 0
while i < len(code):
    pair = code[i:i+2]
    if depth:
        if pair == '/-': depth += 1; i += 2; continue
        if pair == '-/': depth -= 1; i += 2; continue
        i += 1; continue
    if quoted:
        if code[i] == '\\': i += 2; continue
        if code[i] == '"': quoted = False
        i += 1; continue
    if pair == '/-': depth = 1; i += 2; continue
    if pair == '--':
        end = code.find('\n', i)
        i = len(code) if end < 0 else end
        continue
    if code[i] == '"': quoted = True; i += 1; continue
    if code[i] in '([{': stack.append((code[i], i))
    if code[i] in ')]}':
        assert stack and stack[-1][0] == {')':'(', ']':'[', '}':'{'}[code[i]], i
        stack.pop()
    i += 1
assert not stack and not depth and not quoted
imports = re.findall(r'(?m)^import (\S+)', code)
parents, candidates = [], []
with ARCHIVE.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest().upper() == PIN
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for module in imports:
        member = 'lean/' + module.replace('.', '/') + '.lean'
        if member in routes:
            row = routes[member]
            raw = Path(row['captured_source']).read_bytes()
            cap = S / row['capture'] / 'index.json'
            capraw = cap.read_bytes()
            assert sha(raw) == row['sha256'] and len(raw) == row['bytes']
            assert sha(capraw) == row['capture_index_sha256']
            assert row['sha256'] in capraw.decode('utf-8')
            candidates.append(dict(module=module, path=row['captured_source'],
                bytes=len(raw), sha256=sha(raw), capture_index=str(cap),
                capture_sha256=sha(capraw), accepted=False))
        else:
            raw = archive.extractfile(member).read()
            assert raw == (REF / member).read_bytes()
            parents.append(dict(module=module, member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['independent_product_event_mass', 'actual_visible_table_depends_only_on_question',
    'assignment_acceptance_mass_bounds', 'favorable_private_assignment_mass_eq_matching']
assert definitions == ['independentProduct', 'visibleQuestionTable', 'visibleQuestionOutputLaw',
    'assignmentAccepts', 'assignmentAcceptanceEvent', 'assignmentPairLaw']
checks = 'import PvNP.RealizableHardness.ActualPrivateAssignmentLaw\n\n'
for name in definitions + exports:
    checks += '#check PvNP.RealizableHardness.ActualPrivateAssignmentLaw.' + name + '\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualPrivateAssignmentLaw.' + name + '\n'
plan_relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan_raw = subprocess.run(['git', '-C', str(P), 'show', 'b353bb8:' + plan_relative],
    check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Literal private-output product and assignment acceptance'
plan = plan_raw.decode('utf-8')
assert plan.count(heading) == 1
section = plan[plan.index(heading):].split('\n## ', 1)[0]
argument = '# Actual private assignment law\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n' + section
argument += ('\n\nThis module translates the normalized product, visible-question table factorization, '
    'literal assignment event and same-selected-pair conditional identity. Its unconditional '
    'score bounds follow from nonnegative normalized finite weights. It supplies neither a '
    'game-success hypothesis nor a new counting assumption. Full supplied-vector and original '
    'question-law composition, imported source-game strategy-domain identification, count '
    'applicability and every accepted-parent/kernel/review gate remain required.\n')
for name, raw in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(raw, encoding='utf-8', newline='\n')
mathlib = REF / 'external/Mathlib/Data/Fintype/BigOperators.lean'
mathlib_raw = mathlib.read_bytes()
files = []
for path in sorted(OUT.iterdir()):
    assert path.is_file()
    raw = path.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, source_only_lexical_preflight=True, independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    parent_dependencies=parents, candidate_dependencies=candidates, direct_imports=imports,
    dependency_inventory=dict(path=str(inventory_path), sha256=sha(inventory_raw)),
    historical_dependency_pins_unchanged=True, accepted_operator_rebind_required=True,
    inherited_dependency_successor_bindings=inventory['known_selected_dependency_successors'],
    planning_argument=dict(repository=str(P), relative_path=plan_relative, committed_head='b353bb8',
        committed_blob_sha256=sha(plan_raw), heading=heading, section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    mathlib_source_dependencies=[dict(path=str(mathlib), bytes=len(mathlib_raw), sha256=sha(mathlib_raw))],
    public_axiom_requests=exports, checked_definitions=definitions,
    normalized_independent_private_outputs=True, visible_table_has_no_original_question_argument=True,
    same_selected_pair=True, literal_conditional_assignment_event_identity=True,
    assignments_for_all_matching_outputs=True, original_question_law_identified=False,
    full_vector_strategy_identified=False, full_source_game_law_identified=False,
    source_no_proved=False, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), candidate_imports=len(candidates),
    parent_imports=len(parents), public_theorems=len(exports), public_definitions=len(definitions))))
