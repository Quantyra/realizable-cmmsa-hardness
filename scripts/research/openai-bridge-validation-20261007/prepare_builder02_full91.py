"""Freeze additive independent-source-size successor; no cloud or compiler call."""
import copy
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from prepare_builder02 import sha

PARENT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02')
OUTPUT = PARENT.parent / 'full91-source-size-resource02'
CANDIDATES = Path(__file__).parent / 'full91-source-size-candidate-v1'
HARNESS = 'fresh-integrated-axioms.lean'
REQUESTS = [
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment.selected_actual_append_moment',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment.selected_actual_center_identity',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment.selected_actual_source_dimension_bound',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment.selected_actual_material_moment_bound',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeOriginalApplication.selected_actual_material_moment_bound_original',
]


def parent_custody():
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check / 'terminal-custody.json').read_bytes())
    termination = json.loads((check / 'vm-termination.json').read_bytes())
    qualified_path = check / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    assert digest(qualified_path) == 'C647876E7AA829D0707216F4BC0288F008F003A0D29659483DD9D4E5859BBA91'
    qualified = json.loads(qualified_path.read_bytes())
    assert terminal['run'] == termination['run'] == marker['run']
    assert qualified['all_seven_stage_exits'] == [0] * 7
    assert qualified['full_original_A22_HC46_selected_native_gates_green']
    assert qualified['full90_expanded_native_gates_green']
    assert qualified['expanded_requested_axiom_count'] == 173
    assert termination['custody_verified_before_stop']
    assert termination['independent']['id'] == '7237681467779354904'
    assert termination['independent']['status'] == 'TERMINATED'
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    return marker, custody


def validate_expansion(old, new, derivation):
    added = [row['candidate_path'] for row in derivation['artifacts']]
    assert set(new) == set(old) | set(added)
    changed = sorted(name for name in old if old[name] != new[name])
    assert changed == sorted([HARNESS, 'capture-manifest.json'])
    for row in derivation['artifacts']:
        assert sha(old[row['parent_path']]) == row['parent_sha256']
        assert sha(new[row['candidate_path']]) == row['candidate_sha256']
        assert len(new[row['candidate_path']]) == row['bytes']
    assert new[HARNESS] == old[HARNESS] + ''.join('#print axioms ' + r + '\n' for r in REQUESTS).encode()
    a = json.loads(old['capture-manifest.json'])
    b = json.loads(new['capture-manifest.json'])
    assert len(a['project_sources']) == 319 and len(b['project_sources']) == 322
    assert len(a['requested_axioms']) == 173 and b['requested_axioms'] == a['requested_axioms'] + REQUESTS
    assert b['stages'][4]['argv'] == a['stages'][4]['argv'] + [
        'PvNP.RealizableHardness.' + Path(rel).stem for rel in added]
    for rel in added:
        pin = b['project_sources'].pop(rel)
        assert pin['sha256'] == sha(new[rel]) and pin['bytes'] == len(new[rel])
    b['requested_axioms'] = a['requested_axioms']
    b['stages'][4] = a['stages'][4]
    assert b == a, 'Unauthorized stage/config/compiler/cache/claims change'
    return changed, added


def main():
    from full90_capture_gates import validate_successor
    validate_successor()
    marker, custody = parent_custody()
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = dict(old)
    derivation = json.loads((CANDIDATES / 'derivation.json').read_bytes())
    manifest = copy.deepcopy(json.loads(old['capture-manifest.json']))
    for row in derivation['artifacts']:
        rel = row['candidate_path']
        data = (CANDIDATES / Path(rel).name).read_bytes()
        assert sha(data) == row['candidate_sha256']
        new[rel] = data
        manifest['project_sources'][rel] = {'sha256': sha(data), 'bytes': len(data)}
        manifest['stages'][4]['argv'].append('PvNP.RealizableHardness.' + Path(rel).stem)
    manifest['requested_axioms'].extend(REQUESTS)
    new[HARNESS] += ''.join('#print axioms ' + r + '\n' for r in REQUESTS).encode()
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    changed, added = validate_expansion(old, new, derivation)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = {'schema': 'full91-additive-source-size-expansion-v1',
                 'parent_run': marker['run'], 'parent_custody': custody,
                 'added_sources': added, 'additional_profiles': REQUESTS,
                 'original319_sources_preserved': True, 'original173_requests_preserved': True,
                 'original_seven_stage_commands_preserved_as_prefixes': True,
                 'compiler_packages_core_cache_configs_preserved': True,
                 'derivation_sha256': digest(CANDIDATES / 'derivation.json'),
                 'local_compilation': False, 'native_verification_pending': True,
                 'launch_clearance': False, 'accepted': False}
    (OUTPUT / 'source-expansion.json').write_text(json.dumps(expansion, indent=2) + '\n', encoding='utf-8')
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'),
                     parent_run=marker['run'], source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                     changed_files=changed, added_files=added, project_sources_preserved=319,
                     original173_requests_preserved=True, additional_profiles=REQUESTS,
                     auxiliary_inputs={n: sha(new[n]) for n in binding['auxiliary_inputs']},
                     files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    successor.pop('added_request', None)
    (OUTPUT / 'resource-binding.json').write_text(json.dumps(successor, indent=2) + '\n', encoding='utf-8')
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps({'root': str(OUTPUT), 'sources': 322, 'profiles': 178,
                      'archive_sha256': digest(OUTPUT / 'input-archive.tar.gz'),
                      'launch_clearance': False, 'accepted': False}))


if __name__ == '__main__':
    main()
