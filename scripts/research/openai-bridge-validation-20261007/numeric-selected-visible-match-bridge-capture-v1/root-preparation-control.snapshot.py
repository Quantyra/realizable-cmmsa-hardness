from pathlib import Path
import hashlib, json, re, subprocess, tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-selected-visible-match-bridge-offer-20261011-v1'
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
inventory_path = S / 'complete-numeric-source-only-inventory-v15.json'
inventory_raw = inventory_path.read_bytes()
assert sha(inventory_raw) == 'DF4888CA1D5AFB8280F6CAE4DFB7ACA5848DAD9578A3B0D221A2300FEC101A6A'
inventory = json.loads(inventory_raw)
routes = {row['path']: row for row in inventory['selected_sources']}
source = (OUT / 'ActualSelectedVisibleMatchBridge.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert all(x not in code for x in ['\ufffd', '\u00e2\u02c6', '\u00e2\u2020', '\\sum', '\\r\\n'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
stack = []
depth = 0
quoted = False
i = 0
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
        assert module.startswith('PvNP.RealizableHardness.')
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
            assert raw == (S/'full107-trace-qualified-source-record-v1/review-sources'/member).read_bytes()
            parents.append(dict(module=module, member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['selected_visible_event_actual_matching_and_assignments']
checks = (OUT / 'Checks.lean').read_text(encoding='utf-8')
assert checks.count('#print axioms ') == 1
assert '#print axioms PvNP.RealizableHardness.ActualSelectedVisibleMatchBridge.' + exports[0] in checks
plan_relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan_raw = subprocess.run(['git', '-C', str(P), 'show', 'b353bb8:' + plan_relative],
    check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Literal private-output product and assignment acceptance'
plan = plan_raw.decode('utf-8')
assert plan.count(heading) == 1
section = plan[plan.index(heading):].split('\n## ', 1)[0]
upstream = S / 'numeric-global-full-vector-event-capture-v1/index.json'
assert sha(upstream.read_bytes()) == '6A27EE5BD56A4115DF3B07BA147CAD681336C4E5E2369B59C34EFFC8271D1910'
files = []
for path in sorted(OUT.rglob('*')):
    if not path.is_file(): continue
    raw = path.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    files.append(dict(path=path.relative_to(OUT).as_posix(), bytes=len(raw),
        sha256=sha(raw), candidate_scope='diagnostics' not in path.parts))
manifest = dict(schema=OUT.name, author='/root', initial_author='/root/fixed_score_recovery',
    story='E002/S3137', accepted=False, compiler_invoked=False,
    source_only_lexical_preflight=True, independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    parent_dependencies=parents, candidate_dependencies=candidates, direct_imports=imports,
    dependency_inventory=dict(path=str(inventory_path), sha256=sha(inventory_raw)),
    historical_dependency_pins_unchanged=True, accepted_operator_rebind_required=True,
    inherited_dependency_successor_bindings=inventory['known_selected_dependency_successors'],
    semantic_upstream_full_vector=dict(path=str(upstream), sha256=sha(upstream.read_bytes()), accepted=False),
    planning_argument=dict(repository=str(P), relative_path=plan_relative, committed_head='b353bb8',
        committed_blob_sha256=sha(plan_raw), heading=heading, section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=[],
    literal_selected_event_instantiated=True, same_selected_pair=True,
    canonical_to_actual_agreement_transport=True, assignments_for_all_matching_outputs=True,
    original_rank_stability_required=False, original_window_supported_required=False,
    second_side_loss_charged=False, game_law_identified=False, source_no_proved=False,
    author_checkpoint_sha256='DC881A7883B02216FEA9BB56885DB652E99B1847E66135B1D12C993F9AB7A98B',
    author_service_failure_ids=['960b1d2f-6d95-45b0-9e50-b0e08ea76830', '55054cc7-450b-4e78-a734-dcc8245a2de1'],
    files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), candidate_imports=len(candidates),
    parent_imports=len(parents), public_theorems=len(exports), files=len(files))))
