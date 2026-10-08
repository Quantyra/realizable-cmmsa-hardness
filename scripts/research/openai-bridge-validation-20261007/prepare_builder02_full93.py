"""Freeze warning repairs and manuscript-compatible moment consumer; no launch."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full92 import OUTPUT as PARENT

HERE = Path(__file__).parent
OUTPUT = PARENT.parent / 'full93-manuscript-moment-resource02'
WARNINGS = HERE / 'full93-warning-candidate-v1'
DYADIC = HERE / 'manuscript-dyadic-moment-candidate-v1'
MODULE = 'PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment'
ADDED = 'lean/' + MODULE.replace('.', '/') + '.lean'
HARNESS = 'fresh-integrated-axioms.lean'
REQUESTS = [MODULE + '.' + name for name in [
    'selected_actual_HC_spectral_moment_bound_at_dyadic_exponent',
    'selected_actual_material_moment_bound_at_dyadic_exponent',
    'selected_actual_material_moment_bound_original_at_dyadic_exponent',
]]
REPORT_SHA = '7BCABFD4639764A311BF82584791060DF02A5DA226BD7F58DB9DAB41A050B93F'


def parent_custody():
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    report_path = check / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    assert digest(report_path) == REPORT_SHA
    report = json.loads(report_path.read_bytes())
    assert terminal['run'] == stop['run'] == marker['run']
    assert terminal['terminal']['native_terminal'] and terminal['terminal']['compile_green']
    assert [s['native_exit'] for s in terminal['terminal']['stages']] == [0] * 7
    assert report['all_seven_stage_exits'] == [0] * 7
    assert report['expanded_requested_axiom_count'] == 178
    assert report['project_closure_sources'] == 322
    assert report['owned_warning_headers'] == [0, 0, 0, 0, 21, 0, 0]
    assert report['inherited_regression_headers'] == [0] * 7
    assert report['owned_error_headers'] == report['bad_profiles'] == report['missing_objects'] == 0
    assert not report['full92_expanded_native_gates_green']
    assert stop['custody_verified_before_stop']
    assert stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    return marker, custody


def make_successor(old):
    warning = json.loads((WARNINGS / 'derivation.json').read_bytes())
    dyadic = json.loads((DYADIC / 'derivation.json').read_bytes())
    assert digest(PARENT / 'input-archive.tar.gz') == warning['parent_archive_sha256']
    new = dict(old)
    manifest = copy.deepcopy(json.loads(old['capture-manifest.json']))
    for row in warning['sources']:
        rel = row['path']
        data = (WARNINGS / Path(rel).name).read_bytes()
        assert sha(old[rel]) == row['old_sha256']
        assert sha(data) == row['new_sha256'] and len(data) == row['bytes']
        new[rel] = data
        manifest['project_sources'][rel] = {'sha256': sha(data), 'bytes': len(data)}
    assert dyadic['parent_analytic_candidate_sha256'] == warning['sources'][1]['new_sha256']
    data = (DYADIC / Path(ADDED).name).read_bytes()
    assert sha(data) == dyadic['candidate_sha256'] and len(data) == dyadic['bytes']
    new[ADDED] = data
    manifest['project_sources'][ADDED] = {'sha256': sha(data), 'bytes': len(data)}
    manifest['stages'][4]['argv'].append(MODULE)
    manifest['requested_axioms'].extend(REQUESTS)
    new[HARNESS] = ('import ' + MODULE + '\n').encode() + old[HARNESS] + ''.join(
        '#print axioms ' + request + '\n' for request in REQUESTS).encode()
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    validate_expansion(old, new)
    return new


def validate_expansion(old, new):
    warning = json.loads((WARNINGS / 'derivation.json').read_bytes())
    dyadic = json.loads((DYADIC / 'derivation.json').read_bytes())
    repaired = [row['path'] for row in warning['sources']]
    assert set(new) == set(old) | {ADDED}
    assert sorted(n for n in old if old[n] != new[n]) == sorted(repaired + [HARNESS, 'capture-manifest.json'])
    for row in warning['sources']:
        assert sha(old[row['path']]) == row['old_sha256']
        assert sha(new[row['path']]) == row['new_sha256']
    assert sha(new[ADDED]) == dyadic['candidate_sha256']
    assert new[HARNESS] == ('import ' + MODULE + '\n').encode() + old[HARNESS] + ''.join(
        '#print axioms ' + request + '\n' for request in REQUESTS).encode()
    a = json.loads(old['capture-manifest.json'])
    b = json.loads(new['capture-manifest.json'])
    assert len(a['project_sources']) == 322 and len(b['project_sources']) == 323
    assert len(a['requested_axioms']) == 178 and b['requested_axioms'] == a['requested_axioms'] + REQUESTS
    assert b['stages'][4]['argv'] == a['stages'][4]['argv'] + [MODULE]
    for rel in repaired + [ADDED]:
        pin = b['project_sources'][rel]
        assert pin == {'sha256': sha(new[rel]), 'bytes': len(new[rel])}
    b['project_sources'].pop(ADDED)
    for rel in repaired:
        b['project_sources'][rel] = a['project_sources'][rel]
    b['requested_axioms'] = a['requested_axioms']
    b['stages'][4] = a['stages'][4]
    assert b == a, 'Unauthorized stage/config/compiler/cache/claims change'
    modules = {rel[5:-5].replace('/', '.'): rel for rel in a['project_sources']}
    modules[MODULE] = ADDED
    def imports(data):
        return [name for line in re.findall(r'(?m)^import\s+([^\n]+)', data.decode())
                for name in line.split() if name in modules]
    pending, reached = imports(new[HARNESS]), set()
    while pending:
        module = pending.pop()
        if module not in reached:
            reached.add(module)
            pending.extend(imports(new[modules[module]]))
    for request in json.loads(new['capture-manifest.json'])['requested_axioms']:
        owner = max((m for m in modules if request.startswith(m + '.')), key=len)
        assert owner in reached, 'Unimported requested owner: ' + owner
    return repaired


def main():
    from full92_capture_gates import validate_successor
    validate_successor()
    marker, custody = parent_custody()
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = make_successor(old)
    repaired = validate_expansion(old, new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = {
        'schema': 'full93-warning-and-manuscript-dyadic-expansion-v1',
        'parent_run': marker['run'], 'parent_custody': custody,
        'parent_qualified_report_sha256': REPORT_SHA,
        'repaired_sources': repaired, 'added_sources': [ADDED],
        'additional_profiles': REQUESTS, 'original319_sources_preserved': True,
        'parent320_source_bytes_preserved': True, 'all178_requests_preserved': True,
        'original_seven_stage_commands_preserved_as_prefixes': True,
        'compiler_packages_core_cache_configs_preserved': True,
        'warning_derivation_sha256': digest(WARNINGS / 'derivation.json'),
        'dyadic_derivation_sha256': digest(DYADIC / 'derivation.json'),
        'original_fixed_window_theorems_retained': True,
        'local_compilation': False, 'native_verification_pending': True,
        'numeric_NO_proven': False, 'launch_clearance': False, 'accepted': False,
    }
    (OUTPUT / 'source-expansion.json').write_text(json.dumps(expansion, indent=2) + '\n', encoding='utf-8')
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'),
                     parent_run=marker['run'], source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                     changed_files=sorted(repaired + [HARNESS, 'capture-manifest.json']),
                     added_files=[ADDED], project_sources_preserved=320,
                     additional_profiles=REQUESTS,
                     auxiliary_inputs={n: sha(new[n]) for n in binding['auxiliary_inputs']},
                     files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    (OUTPUT / 'resource-binding.json').write_text(json.dumps(successor, indent=2) + '\n', encoding='utf-8')
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps({'root': str(OUTPUT), 'sources': 323, 'profiles': 181,
                      'input_sha256': digest(OUTPUT / 'input-archive.tar.gz'),
                      'launch_clearance': False, 'accepted': False}))


if __name__ == '__main__':
    main()
