"""Five disjoint source successors adding only verified namespace opens."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
report_path = S/'numeric-decay-namespace-inspection-v1'/'result.json'
report_raw = report_path.read_bytes()
assert sha(report_raw) == '4D58833B8EB06297E79C37D53EF5FA9F0184622C7D4F406C47F9562224FCC858'
report = json.loads(report_raw)
assert len(report['findings']) == 5
OUT = S/'numeric-decay-namespace-repair-offer-20261011-v1'
OUT.mkdir(exist_ok=False)
records = []
for row in report['findings']:
    parent_path = Path(row['captured_source'])
    original = parent_path.read_bytes()
    assert sha(original) == row['sha256']
    index_path = parent_path.parent/'index.json'
    index = index_path.read_bytes()
    assert sha(index) == row['capture_index_sha256']
    original_manifest_path = parent_path.parent/'manifest.json'
    original_manifest = original_manifest_path.read_bytes()
    namespaces = sorted({item['namespace'] for item in row['missing']})
    newline = b'\r\n' if b'\r\n' in original else b'\n'
    marker = newline+b'set_option autoImplicit false'
    assert original.count(marker) == 1
    insertion = newline+('open '+' '.join(namespaces)).encode()+newline
    updated = original.replace(marker, insertion+marker, 1)
    assert updated.replace(insertion+marker, marker, 1) == original
    module = parent_path.stem
    target = OUT/parent_path.name
    target.write_bytes(updated)
    checks_parent = parent_path.parent/'Checks.lean'
    checks = checks_parent.read_bytes()
    original_checks_pin = next(x['sha256'] for x in json.loads(original_manifest)['files'] if x['path'] == 'Checks.lean')
    assert sha(checks) == original_checks_pin
    checks_target = OUT/(module+'Checks.lean')
    checks_target.write_bytes(checks)
    code = updated.decode('utf-8')
    imports = re.findall(r'(?m)^import (\S+)', code)
    assert imports == re.findall(r'(?m)^import (\S+)', original.decode('utf-8'))
    records.append(dict(module='PvNP.RealizableHardness.'+module, path=target.name,
        bytes=len(updated), sha256=sha(updated), parent_source=str(parent_path),
        parent_source_sha256=sha(original), parent_capture_index=str(index_path),
        parent_capture_index_sha256=sha(index), parent_manifest=str(original_manifest_path),
        parent_manifest_sha256=sha(original_manifest), added_namespaces=namespaces,
        exact_inverse_byte_check=True, declarations_proofs_imports_unchanged=True,
        checks_path=checks_target.name, checks_parent=str(checks_parent), checks_sha256=sha(checks),
        checks_unchanged=True, direct_imports=imports,
        source_only_lexical_preflight=inspect_bytes(updated, target.name),
        original_dependency_pins_retained_in_parent_manifest=True,
        execution_dependency_rebind_required=True, accepted=False))
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan = subprocess.run(['git','-C',str(P),'show','d262519:'+relative], check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Concrete total iid strategy composition and namespace repair'
text = plan.decode()
assert text.count(heading) == 1
section = text[text.index(heading):].split('\n## ',1)[0]
(OUT/'ARGUMENT.md').write_text('# Source-only namespace repairs\n\n'+section+'\n', encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, mathematical_changes=False, independent_static_review_completed=False,
    inspection=dict(path=str(report_path), sha256=sha(report_raw)), source_successors=records,
    planning_argument=dict(repository=str(P), relative_path=relative, committed_head='d262519',
        committed_blob_sha256=sha(plan), heading=heading, section_sha256=sha(section.encode())),
    toolchain='leanprover/lean4:v4.34.0-rc2', mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    historical_pins_and_metadata_unchanged=True, explicit_execution_rebind_required=True,
    inherited_global_posterior_source_game_true_rejected=True,
    source_game_law_identified=False, source_no_proved=False,
    files=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir()) if p.is_file()])
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(manifest_sha256=sha((OUT/'manifest.json').read_bytes()),
    source_successors=[dict(module=r['module'],sha256=r['sha256']) for r in records])))
