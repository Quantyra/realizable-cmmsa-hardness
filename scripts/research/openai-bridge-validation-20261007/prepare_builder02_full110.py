"""Freeze the complete exact real/complex operator batch; no launch or compiler."""
import copy
from datetime import datetime, timezone
import gzip
import io
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from prepare_complete_operator_scope_v2 import HERE, PARENT, HARNESS, parent, make_successor, additions, validate, sha

OUTPUT = PARENT.parent / 'full110-exact-real-complex-operators-resource02'
PROPOSAL_PIN = 'D0FAA95714A0278FA0232453342F5BC1F0A25D596FE62CA067D062D6973BCC02'
QUALIFIED_PIN = '467EB67622142D6B1A959F4C7D20510B6A785D430BB91C6D9F0435F20D5FECA4'
PARENT_BINDING_PIN = '6A793C3D4DF1DDA09933FAEA491F28A51D017061F19F856B882CA72A0BF49655'
NATIVE_PIN = 'BD8EC70F9A138EBB5C3AC8E52B7732CF7CFE3D3E5C9B9F8CB3FB16FE37F21154'
RUN = 'cmmsa_a8_output_20261010T110328Z_0d5c26f4'
RESERVE = 1536 * 1024**2


def write_json(path, value):
    path.open('x', encoding='utf-8').write(json.dumps(value, indent=2) + '\n')


def parent_native_custody():
    marker_path = PARENT / 'launch-once.json'
    marker = json.loads(marker_path.read_bytes())
    assert marker['run'] == RUN
    check = Path(marker['preflight'])
    assert check.resolve().is_relative_to(PARENT.resolve())
    files = dict(launch_marker=marker_path, terminal=check / 'terminal-custody.json',
                 historical_stop=check / 'vm-termination.json',
                 qualified=check / 'qualified-native' / RUN / 'material-expanded-native-report.json',
                 resource_binding=PARENT / 'resource-binding.json')
    terminal, stop, qualified = [json.loads(files[name].read_bytes()) for name in ('terminal', 'historical_stop', 'qualified')]
    assert terminal['run'] == stop['run'] == qualified['run'] == RUN
    assert terminal['terminal']['native_terminal'] and terminal['terminal']['compile_green']
    assert [row['native_exit'] for row in terminal['terminal']['stages']] == [0] * 7
    assert qualified['full109_expanded_native_gates_green'] and not qualified['accepted']
    assert qualified['project_closure_sources'] == 348
    assert qualified['owned_warning_headers'] == qualified['inherited_regression_headers'] == [0] * 7
    assert digest(files['qualified']) == QUALIFIED_PIN
    assert digest(files['resource_binding']) == PARENT_BINDING_PIN
    assert marker['remote_controls']['resource-binding.json'] == PARENT_BINDING_PIN
    assert stop['custody_verified_before_stop'] and not stop['other_vm_modified']
    assert stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    custody = terminal['custody']
    assert custody['remote_sha256'] == NATIVE_PIN and custody['bytes'] == 39707053
    verify_local_custody(custody['short_path'], custody['repository_path'], NATIVE_PIN, custody['bytes'])
    return custody, files


def main():
    assert not OUTPUT.exists(), 'Never overwrite a frozen successor'
    assert digest(HERE / 'prepare_complete_operator_scope_v2.py') == '892D56612F03C3ED79E1E006B6340B7BC8F3721222CFCA59E5079B8CB2C9B196'
    custody, evidence = parent_native_custody()
    old = parent()
    new = make_successor(old)
    sources, requests, provenance = additions()
    assert len(sources) == 21 and len(requests) == 86
    proposal_path = HERE / 'complete-real-complex-operator-full-scope-proposal-v2.json'
    assert digest(proposal_path) == PROPOSAL_PIN
    proposal = json.loads(proposal_path.read_bytes())
    assert sha(new['capture-manifest.json']) == proposal['generated_manifest_sha256']
    assert sha(new[HARNESS]) == proposal['generated_harness_sha256']
    assert all(row['rejected'] for row in proposal['negative_scope_checks'])
    before_free = shutil.disk_usage(OUTPUT.parent).free
    assert before_free >= RESERVE + 2 * sum(len(data) for data in new.values())
    OUTPUT.mkdir(exist_ok=False)
    with (OUTPUT / 'input-archive.tar.gz').open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as archive:
                for name, data in sorted(new.items()):
                    assert not name.startswith(('/', '\\')) and '..' not in Path(name).parts
                    member = tarfile.TarInfo(name)
                    member.size = len(data)
                    member.mode = 0o644
                    member.mtime = 0
                    archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').open('xb').write(new['capture-manifest.json'])
    expansion = dict(schema='full110-full369-full347-exact-real-complex-operators-v1',
                     parent_run=RUN, parent_custody=custody, parent_qualified_report_sha256=QUALIFIED_PIN,
                     parent_qualified_native_green=True, parent_material_accepted=False,
                     parent_trace_and_independent_crosslevel_review_pending=True,
                     parent_termination_is_historical_not_current_vm_state=True,
                     added_sources=provenance, additional_profiles=requests, repaired_parent_sources=[],
                     all348_parent_source_bytes_and261_profiles_preserved=True,
                     all_seven_parent_stage_prefixes_preserved=True,
                     entire369_source_graph_reachable=True, all21_added_sources_owned=True,
                     compiler_package_core_warm_cache_configuration_preserved=True,
                     scope_proposal_sha256=PROPOSAL_PIN, exact_real_complex_operator_and_two_function_targets=True,
                     whole_complex_hypercontractivity_appendix_certified=False,
                     native_verification_pending=True, independent_material_review_pending=True,
                     numeric_NO_proven=False, R14='HIGH open', compiler_invoked=False,
                     cloud_operation=False, launch_clearance=False, accepted=False, full_goal_complete=False)
    write_json(OUTPUT / 'source-expansion.json', expansion)
    binding = copy.deepcopy(json.loads(evidence['resource_binding'].read_bytes()))
    binding.update(parent_resource_binding_sha256=PARENT_BINDING_PIN, parent_run=RUN,
                   source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                   changed_files=[HARNESS, 'capture-manifest.json'], added_files=list(sources),
                   project_sources_preserved=348, additional_profiles=requests,
                   auxiliary_inputs={name: sha(new[name]) for name in binding['auxiliary_inputs']},
                   files={name: digest(OUTPUT / name) for name in ('input-archive.tar.gz', 'capture-manifest.json')},
                   parent_trace_and_independent_review_pending=True,
                   parent_termination_is_historical_not_current_vm_state=True,
                   compiler_invoked=False, launch_clearance=False)
    write_json(OUTPUT / 'resource-binding.json', binding)
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    validate(old, capsule(OUTPUT / 'input-archive.tar.gz'))
    provenance_dir = OUTPUT / 'parent-provenance'
    provenance_dir.mkdir()
    records = []
    for label, path in evidence.items():
        data = path.read_bytes()
        copy_path = provenance_dir / (label + '.json')
        copy_path.open('xb').write(data)
        assert copy_path.read_bytes() == path.read_bytes()
        records.append(dict(original=str(path), copy=copy_path.relative_to(OUTPUT).as_posix(),
                            bytes=len(data), sha256=sha(data)))
    receipt = dict(prepared_utc=datetime.now(timezone.utc).isoformat(), root=str(OUTPUT),
                   sources=369, profiles=347, capsule_members=len(new),
                   input_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
                   manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
                   local_free_before=before_free, local_free_after=shutil.disk_usage(OUTPUT).free,
                   unchanged_minimum_local_reserve_bytes=RESERVE,
                   complete_archive_roundtrip_and_scope_validation=True,
                   parent_native_two_copy_custody_reverified=True, parent_provenance=records,
                   current_authenticated_vm_state_known=False,
                   parent_trace_and_independent_review_pending=True,
                   no_source_staging_or_recovery_replay=True, no_vm_power_or_compiler_operation=True,
                   launch_clearance=False, native_verified=False, accepted=False)
    assert receipt['local_free_after'] >= RESERVE
    write_json(OUTPUT / 'freeze-receipt.json', receipt)
    print(json.dumps({k: receipt[k] for k in ('root', 'sources', 'profiles', 'capsule_members',
                       'input_sha256', 'manifest_sha256', 'launch_clearance', 'native_verified')}))


if __name__ == '__main__':
    main()
