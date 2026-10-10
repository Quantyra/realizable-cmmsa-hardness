"""Freeze the full-scope two-alias repair of settled Full108 owned warnings."""
import copy
import io
import json
import re
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from prepare_builder02_full108 import OUTPUT as PARENT, REQUESTS
from prepare_builder02_full103 import headers

HERE = Path(__file__).parent
REPAIRS = HERE/'append-product-crosslevel-warning-repair-candidate-v1'
SOURCE = 'lean/PvNP/RealizableHardness/ActualAppendProductCrossLevelIdentity.lean'
REPAIR_FILE = REPAIRS/'ActualAppendProductCrossLevelIdentity.lean'
OUTPUT = PARENT.parent/'full109-exact-crosslevel-warning-repair-resource02'


def validate_expansion(old, new):
    repair = json.loads((REPAIRS/'derivation.json').read_bytes())
    assert repair['source'] == SOURCE
    assert set(old) == set(new)
    assert {p for p in old if old[p] != new[p]} == {SOURCE, 'capture-manifest.json'}
    before, after = old[SOURCE], new[SOURCE]
    expected = before.decode('utf-8')
    assert expected.count('if_pos') == expected.count('if_neg') == 1
    expected = expected.replace('if_pos', 'ite_eq_left').replace('if_neg', 'ite_eq_right')
    assert after == expected.encode() == REPAIR_FILE.read_bytes()
    assert headers(before) == headers(after) and len(headers(after)) == len(headers(before))
    assert not after.startswith(b'\xef\xbb\xbf')
    assert not re.search(r'(?m)^\s*set_option linter\.', after.decode())
    a, b = [json.loads(data) for data in [old['capture-manifest.json'], new['capture-manifest.json']]]
    assert len(b['project_sources']) == 348 and len(b['requested_axioms']) == 261 and len(b['stages']) == 7
    assert a['project_sources'][SOURCE]['sha256'] == repair['old_sha256']
    assert b['project_sources'][SOURCE] == dict(sha256=repair['new_sha256'], bytes=len(after))
    assert digest(REPAIR_FILE) == repair['new_sha256']
    normalized = copy.deepcopy(b)
    normalized['project_sources'][SOURCE] = a['project_sources'][SOURCE]
    assert normalized == a, 'Only one proof source pin may change'
    return True


def main():
    from full108_capture_gates import validate_successor
    validate_successor()
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    stop = json.loads((check/'vm-termination.json').read_bytes())
    assert marker['run'] == terminal['run'] == stop['run']
    assert terminal['terminal']['native_terminal'] and terminal['terminal']['compile_green']
    assert [row['native_exit'] for row in terminal['terminal']['stages']] == [0]*7
    qualified = json.loads((check/'qualified-native'/marker['run']/'material-expanded-native-report.json').read_bytes())
    assert not qualified['full108_expanded_native_gates_green']
    assert qualified['owned_warning_headers'] == [0,0,0,0,2,2,0]
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == '7237681467779354904'
    repair = json.loads((REPAIRS/'derivation.json').read_bytes())
    assert repair['parent_run'] == marker['run'] and repair['parent_native_archive_sha256'] == custody['remote_sha256']
    old = capsule(PARENT/'input-archive.tar.gz')
    new = dict(old)
    new[SOURCE] = REPAIR_FILE.read_bytes()
    manifest = json.loads(old['capture-manifest.json'])
    manifest['project_sources'][SOURCE] = dict(sha256=repair['new_sha256'], bytes=len(new[SOURCE]))
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    validate_expansion(old, new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(schema='full109-full348-full261-two-alias-repair-v1',
        parent_run=marker['run'], parent_custody=custody, parent_native_green=True,
        parent_native_terminal_and_owned_warning_failure_preserved=True, repair_derivation_sha256=digest(REPAIRS/'derivation.json'),
        repaired_sources=[dict(path=SOURCE, original_sha256=repair['old_sha256'], sha256=repair['new_sha256'],
            bytes=len(new[SOURCE]), all_declaration_headers_preserved=True, no_linter_disable_added=True)],
        added_sources=[], additional_profiles=[], parent_capture_sources=348, parent_capture_profiles=261,
        all348_source_paths_and261_profiles_and7_stage_commands_preserved=True,
        all347_other_source_bytes_preserved=True, compiler_invoked=False, native_verification_pending=True,
        launch_clearance=False, accepted=False)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion, indent=2)+'\n').encode())
    binding = json.loads((PARENT/'resource-binding.json').read_bytes())
    binding.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'), changed_files=[SOURCE, 'capture-manifest.json'],
        added_files=[], files={name:digest(OUTPUT/name) for name in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(binding, indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=348, profiles=261,
        input_sha256=digest(OUTPUT/'input-archive.tar.gz'), manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
        launch_clearance=False)))


if __name__ == '__main__':
    main()
