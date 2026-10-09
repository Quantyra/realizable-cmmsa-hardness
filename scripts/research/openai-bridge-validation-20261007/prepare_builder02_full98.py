"""Freeze full327/full192 actual matrix/Fourier bridges; no local Lean or launch."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full97 import OUTPUT as PARENT, REQUESTS as PRIOR_BRIDGES

HERE = Path(__file__).parent
OUTPUT = PARENT.parent / 'full98-actual-matrix-fourier-bridge-resource02'
CANDIDATES = HERE / 'full98-matrix-fourier-candidates-v1'
MODULES = ['PvNP.RealizableHardness.BinaryMatrixRightOrbit',
           'PvNP.RealizableHardness.BinaryMatrixRightFourierCovariance']
ADDED = ['lean/' + m.replace('.', '/') + '.lean' for m in MODULES]
NEW_REQUESTS = [MODULES[0] + '.' + n for n in ['same_range_matrix_right_orbit', 'basis_invariant_eq_of_same_range']]
NEW_REQUESTS += [MODULES[1] + '.' + n for n in ['rightBasisEquiv', 'pairing_mul_right', 'character_mul_right',
    'uniformMean_comp_equiv', 'fourierCoeff_mul_right_of_basis_invariant', 'fourierCoeff_eq_of_same_range']]
REQUESTS = PRIOR_BRIDGES + NEW_REQUESTS
HARNESS = 'fresh-integrated-axioms.lean'
IMPORTS = ''.join('import ' + m + '\n' for m in MODULES).encode()
PRINTS = ''.join('#print axioms ' + r + '\n' for r in NEW_REQUESTS).encode()


def validate_language(data):
    text = data.decode('utf-8', errors='strict')
    assert chr(0xfffd) not in text and not re.search(r'\?(?!_)', text)
    assert text.count('noncomputable section') == 1 and text.count('\nend\nend ') == 1
    assert any(ord(c) > 127 for c in text) and not re.search(r'\b(sorry|admit|axiom)\b', text)


def parent_custody():
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '693105513ECC569B34F027FC31FEC85B2C7747A7338CFDFF7CBE9CBE74E773E4'
    assert terminal['terminal']['compile_green'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904' and marker['run'] == terminal['run'] == stop['run']
    report = check / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    qualified = json.loads(report.read_bytes())
    assert digest(report) == 'DFB65C0D666E4B7F8D4ACA23B07B61E51F64227F0085E27968AF649F74B89452'
    assert qualified['full97_expanded_native_gates_green'] and qualified['all_seven_stage_exits'] == [0]*7
    assert qualified['expanded_requested_axiom_count'] == 184 and qualified['project_closure_sources'] == 325
    assert qualified['owned_warning_headers'] == qualified['inherited_regression_headers'] == [0]*7
    q = PARENT / 'consumption-v1/qualification'
    trace = json.loads((q / 'qualification-summary.json').read_bytes())
    assert trace['structural_trace_qualification'] and trace['nodes'] == 8072 and not any(trace['unresolved_by_graph'].values())
    trace_marker = json.loads((PARENT / 'consumption-v1/launch-once.json').read_bytes())
    trace_check = Path(trace_marker['preflight'])
    trace_custody = json.loads((trace_check / 'terminal-custody.json').read_bytes())['custody']
    verify_local_custody(trace_custody['short_path'], trace_custody['repository_path'], trace_custody['remote_sha256'], trace_custody['bytes'])
    assert trace_custody['remote_sha256'] == '6EC526004C8A69B6F511EFA8446311C88BF73846116067D1733E1A8060F331ED'
    assert json.loads((trace_check / 'vm-termination.json').read_bytes())['independent']['status'] == 'TERMINATED'
    root = json.loads((q / 'material-review-root-reconciliation-v1.json').read_bytes())
    assert root['reports_read_in_full'] and root['all_three_new_body_soundness_checks_passed']
    assert root['all_three_conditional_material_verdicts'] == 'GO-WITH-NOTES, conditional' and not root['full_goal_complete']
    assert len(root['reviews']) == 3
    for row in root['reviews']:
        receipt = json.loads(Path(row['receipt']['path']).read_bytes())
        assert digest(row['receipt']['path']) == row['receipt']['sha256']
        assert digest(row['report']['path']) == receipt['report_sha256'] == row['report']['sha256']
        assert digest(receipt['raw_stdout_path']) == receipt['raw_stdout_sha256']
        assert receipt['actual_packet_context_fit'] and receipt['native_exit'] == 0 and receipt['subagents_spawned'] == 0
    return marker, custody, report, q


def make_successor(old):
    new = dict(old)
    manifest = json.loads(old['capture-manifest.json'])
    rows = {r['name']: r for r in json.loads((CANDIDATES / 'derivation.json').read_bytes())['sources']}
    for rel, module in zip(ADDED, MODULES):
        name = module.rsplit('.', 1)[-1] + '.lean'
        data = (CANDIDATES / name).read_bytes()
        assert sha(data) == rows[name]['sha256'] and len(data) == rows[name]['bytes']
        validate_language(data)
        new[rel] = data
        manifest['project_sources'][rel] = dict(sha256=sha(data), bytes=len(data))
    new[HARNESS] = IMPORTS + old[HARNESS] + PRINTS
    manifest['requested_axioms'] += NEW_REQUESTS
    manifest['stages'][4]['argv'] += MODULES
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    validate_expansion(old, new)
    return new


def validate_expansion(old, new):
    assert set(new) == set(old) | set(ADDED)
    assert sorted(n for n in old if old[n] != new[n]) == sorted([HARNESS, 'capture-manifest.json'])
    assert new[HARNESS] == IMPORTS + old[HARNESS] + PRINTS
    a = json.loads(old['capture-manifest.json'])
    b = json.loads(new['capture-manifest.json'])
    assert len(a['project_sources']) == 325 and len(b['project_sources']) == 327
    assert len(a['requested_axioms']) == 184 and b['requested_axioms'] == a['requested_axioms'] + NEW_REQUESTS
    assert len(set(b['requested_axioms'])) == 192 and len(a['stages']) == len(b['stages']) == 7
    assert b['stages'][4]['argv'] == a['stages'][4]['argv'] + MODULES
    for rel, module in zip(ADDED, MODULES):
        data = (CANDIDATES / (module.rsplit('.', 1)[-1] + '.lean')).read_bytes()
        assert new[rel] == data and b['project_sources'][rel] == dict(sha256=sha(data), bytes=len(data))
        validate_language(data)
    normalized = copy.deepcopy(b)
    for rel in ADDED:
        normalized['project_sources'].pop(rel)
    normalized['requested_axioms'] = a['requested_axioms']
    normalized['stages'][4] = a['stages'][4]
    assert normalized == a, 'Manifest changed beyond exact additive scope'
    modules = {p.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): p for p in b['project_sources']}
    pending = re.findall(r'^import (\S+)', new[HARNESS].decode(), re.M)
    reached = set()
    while pending:
        module = pending.pop()
        if module in reached or module not in modules:
            continue
        reached.add(module)
        pending.extend(re.findall(r'^import (\S+)', new[modules[module]].decode(), re.M))
    assert reached == set(modules), 'All327 project modules must remain reachable'
    return True


def main():
    from full97_capture_gates import validate_successor
    validate_successor()
    marker, custody, report, q = parent_custody()
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = make_successor(old)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(schema='full98-additive-actual-matrix-Fourier-bridge-v1', parent_run=marker['run'], parent_custody=custody,
        parent_qualified_report_sha256=digest(report), parent_trace_qualification_sha256=digest(q / 'qualification-summary.json'),
        parent_review_root_reconciliation_sha256=digest(q / 'material-review-root-reconciliation-v1.json'),
        repaired_sources=[], added_sources=ADDED, additional_profiles=NEW_REQUESTS,
        all325_parent_source_bytes_preserved=True, all184_parent_requests_preserved=True,
        original_seven_stages_preserved_as_prefixes=True, compiler_packages_core_cache_configs_preserved=True,
        candidate_derivation_sha256=digest(CANDIDATES / 'derivation.json'),
        Spectral47_inhabitant_constructed=False, local_compilation=False, native_verification_pending=True,
        launch_clearance=False, accepted=False, full_goal_complete=False)
    (OUTPUT / 'source-expansion.json').write_bytes((json.dumps(expansion, indent=2) + '\n').encode())
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'), changed_files=[HARNESS, 'capture-manifest.json'],
        added_files=ADDED, project_sources_preserved=325, additional_profiles=NEW_REQUESTS,
        auxiliary_inputs={n: sha(new[n]) for n in binding['auxiliary_inputs']},
        files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    (OUTPUT / 'resource-binding.json').write_bytes((json.dumps(successor, indent=2) + '\n').encode())
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=327, profiles=192,
                         input_sha256=digest(OUTPUT / 'input-archive.tar.gz'), launch_clearance=False)))


if __name__ == '__main__':
    main()
