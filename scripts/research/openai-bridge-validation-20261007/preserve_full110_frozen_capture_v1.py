"""Verify and preserve the complete frozen Full110 capsule; never launch or compile."""
import ast
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full110 import OUTPUT, RESERVE, RUN, parent_native_custody
from prepare_complete_operator_scope_v2 import HERE, HARNESS, parent, make_successor, additions, validate, negative_checks, sha

DEST = HERE / 'full110-immutable-capture-record-v1'
AUTH = HERE / 'full109-auth-vm-recheck-20261011T012920Z-61d58f8d'
INPUT_PIN = 'C1702903ECC5F939B9504371D63F0D4313E192446971EF0DD7627F6E770F3C61'
MANIFEST_PIN = '1CA8AE796DAD32C0FF0E4C9DF66D8A0DD1DAADBAA557C325140A61AAD78E12DB'


def verify():
    assert digest(OUTPUT / 'input-archive.tar.gz') == INPUT_PIN
    assert digest(OUTPUT / 'capture-manifest.json') == MANIFEST_PIN
    old, new = parent(), capsule(OUTPUT / 'input-archive.tar.gz')
    assert new == make_successor(old)
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    validate(old, new)
    mutation_results = negative_checks(old, new)
    assert len(mutation_results) == 10 and all(row['rejected'] for row in mutation_results)
    manifest = json.loads(new['capture-manifest.json'])
    assert len(manifest['project_sources']) == 369 and len(manifest['requested_axioms']) == 347
    assert len(manifest['stages']) == 7 and len(new) == 376
    custody, evidence = parent_native_custody()
    sources, requests, provenance = additions()
    expansion = json.loads((OUTPUT / 'source-expansion.json').read_bytes())
    assert expansion['parent_run'] == RUN and expansion['parent_custody'] == custody
    assert expansion['added_sources'] == provenance and expansion['additional_profiles'] == requests
    assert len(sources) == 21 and len(requests) == 86 and expansion['repaired_parent_sources'] == []
    for key in ('native_verification_pending', 'independent_material_review_pending',
                'parent_trace_and_independent_crosslevel_review_pending',
                'parent_termination_is_historical_not_current_vm_state'):
        assert expansion[key] is True
    for key in ('launch_clearance', 'accepted', 'compiler_invoked', 'cloud_operation',
                'full_goal_complete', 'numeric_NO_proven', 'whole_complex_hypercontractivity_appendix_certified'):
        assert expansion[key] is False
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    expected = copy.deepcopy(json.loads(evidence['resource_binding'].read_bytes()))
    expected.update(parent_resource_binding_sha256=digest(evidence['resource_binding']), parent_run=RUN,
                    source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                    changed_files=[HARNESS, 'capture-manifest.json'], added_files=list(sources),
                    project_sources_preserved=348, additional_profiles=requests,
                    auxiliary_inputs={name: sha(new[name]) for name in expected['auxiliary_inputs']},
                    files={'input-archive.tar.gz': INPUT_PIN, 'capture-manifest.json': MANIFEST_PIN},
                    parent_trace_and_independent_review_pending=True,
                    parent_termination_is_historical_not_current_vm_state=True,
                    compiler_invoked=False, launch_clearance=False)
    assert binding == expected, 'Resource/helper/configuration binding drift'
    freeze = json.loads((OUTPUT / 'freeze-receipt.json').read_bytes())
    assert freeze['root'] == str(OUTPUT) and freeze['input_sha256'] == INPUT_PIN
    assert freeze['manifest_sha256'] == MANIFEST_PIN
    assert freeze['sources'] == 369 and freeze['profiles'] == 347 and freeze['capsule_members'] == 376
    assert freeze['unchanged_minimum_local_reserve_bytes'] == RESERVE
    assert freeze['local_free_before'] >= RESERVE and freeze['local_free_after'] >= RESERVE
    assert freeze['parent_native_two_copy_custody_reverified'] is True
    assert freeze['parent_trace_and_independent_review_pending'] is True
    for key in ('native_verified', 'accepted', 'launch_clearance', 'current_authenticated_vm_state_known'):
        assert freeze[key] is False
    assert len(freeze['parent_provenance']) == len(evidence) == 5
    assert {Path(row['original']) for row in freeze['parent_provenance']} == set(evidence.values())
    for row in freeze['parent_provenance']:
        original, saved = Path(row['original']), OUTPUT / row['copy']
        assert saved.resolve().is_relative_to(OUTPUT.resolve())
        data = original.read_bytes()
        assert data == saved.read_bytes() and len(data) == row['bytes'] and sha(data) == row['sha256']
    auth = json.loads((AUTH / 'command.json').read_bytes())
    state = json.loads((AUTH / 'result.json').read_bytes())
    assert auth['native_exit'] == state['native_exit'] == 1
    assert state['exact_authenticated_state'] is None and state['reauthentication_required']
    assert (AUTH / 'control.snapshot.py').read_bytes() == (HERE / 'inspect_full109_auth_vm_state_v1.py').read_bytes()
    assert digest(AUTH / 'control.snapshot.py') == auth['source_sha256']
    for name in ('stdout', 'stderr'):
        assert digest(AUTH / name) == auth[name + '_sha256']
    assert b'Reauthentication failed' in (AUTH / 'stderr').read_bytes()
    assert not state['compiler_invoked'] and not state['vm_power_operation'] and not state['launch_clearance']
    return mutation_results


def main():
    assert not DEST.exists(), 'Never overwrite an immutable custody record'
    mutation_results = verify()
    package = sorted(path for path in OUTPUT.rglob('*') if path.is_file())
    assert len(package) == 10
    controls = [HERE / name for name in (
        'prepare_builder02_full110.py', 'preserve_full110_frozen_capture_v1.py',
        'prepare_complete_operator_scope_v2.py', 'inspect_full109_auth_vm_state_v1.py')]
    for path in controls:
        ast.parse(path.read_text(encoding='utf-8'), filename=str(path))
    inputs = [(path, 'package/' + path.relative_to(OUTPUT).as_posix()) for path in package]
    inputs += [(path, 'controls/' + path.name) for path in controls]
    inputs += [(path, 'authentication/' + path.name) for path in sorted(AUTH.iterdir()) if path.is_file()]
    before = shutil.disk_usage(HERE).free
    assert before >= RESERVE + 2 * sum(path.stat().st_size for path, _ in inputs)
    DEST.mkdir()
    (DEST / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for original, rel in inputs:
        data = original.read_bytes()
        target = DEST / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.open('xb').write(data)
        assert target.read_bytes() == original.read_bytes()
        rows.append(dict(original=str(original), copy=rel, bytes=len(data), sha256=sha(data)))
    assert capsule(DEST / 'package/input-archive.tar.gz') == capsule(OUTPUT / 'input-archive.tar.gz')
    after = shutil.disk_usage(HERE).free
    assert after >= RESERVE
    report = dict(schema='full110-immutable-capture-record-v1', recorded_utc=datetime.now(timezone.utc).isoformat(),
                  files=rows, complete_package_files=10, complete_authentication_files=6,
                  source_count=369, profile_count=347, stage_count=7, added_sources=21, added_profiles=86,
                  input_sha256=INPUT_PIN, manifest_sha256=MANIFEST_PIN,
                  exact_package_roundtrip_and_parent_scope_passed=True,
                  negative_scope_checks=mutation_results, parent_native_two_copy_custody_reverified=True,
                  parent_historical_stop_retained_not_current_vm_state=True,
                  authentication_native_exit=1, current_authenticated_vm_state_known=False,
                  local_free_before=before, local_free_after=after, unchanged_minimum_reserve=RESERVE,
                  parent_trace_and_independent_review_pending=True,
                  cloud_operation=False, lean_executed=False, launch_clearance=False,
                  native_verified=False, accepted=False, full_goal_complete=False)
    (DEST / 'index.json').open('x', encoding='utf-8').write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(destination=str(DEST), preserved_originals=len(rows),
                          archive_sha256=INPUT_PIN, index_sha256=digest(DEST / 'index.json'),
                          scope_mutations_rejected=len(mutation_results), launch_clearance=False,
                          native_verified=False, accepted=False)))


if __name__ == '__main__':
    main()
