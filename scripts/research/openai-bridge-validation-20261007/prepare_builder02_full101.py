"""Freeze additive full340/full251 spectral proof/application; no compiler or cloud."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile

from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule

HERE = Path(__file__).parent
PARENT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
OUTPUT = PARENT.parent / 'full101-spectral-original-application-resource02'
RECOVERED = HERE / 'existing-spectral-candidate-recovery-v1'
CANDIDATES = HERE / 'full101-spectral-original-application-candidate-v1'
HARNESS = 'fresh-integrated-axioms.lean'


def read(path):
    return json.loads(Path(path).read_bytes())


def additions():
    recovery = read(RECOVERED / 'recovery.json')
    derivation = read(CANDIDATES / 'derivation.json')
    rows = recovery['recovered_modules'] + derivation['files']
    sources = {}
    requests = []
    for row in rows:
        rel = row['path']
        directory = RECOVERED if row in recovery['recovered_modules'] else CANDIDATES
        data = (directory / rel.rsplit('/', 1)[1]).read_bytes()
        assert sha(data) == row['sha256'] and len(data) == row['bytes']
        text = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf') and not re.search(r'^\s*-[ \t]+', text, re.M)
        sources[rel] = data
        if rel.endswith('Checks.lean'):
            continue
        namespace = re.search(r'(?m)^namespace (\S+)', text).group(1)
        requests.extend(namespace + '.' + name for name in
                        re.findall(r'(?m)^(?:noncomputable )?(?:theorem|def) (\w+)', text))
    assert len(sources) == 13 and len(requests) == len(set(requests)) == 59
    return sources, requests


def make_successor(old):
    sources, requests = additions()
    new = dict(old)
    manifest = json.loads(old['capture-manifest.json'])
    assert not set(sources) & set(manifest['project_sources'])
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    new.update(sources)
    for rel, data in sources.items():
        manifest['project_sources'][rel] = dict(sha256=sha(data), bytes=len(data))
    manifest['owned_sources'] += list(sources)
    manifest['requested_axioms'] += requests
    manifest['stages'][4]['argv'] += [m for m in modules if not m.endswith('Checks')]
    manifest['stages'][5]['argv'] += [m for m in modules if m.endswith('Checks')]
    imports = ''.join('import ' + m + '\n' for m in modules).encode()
    prints = ''.join('#print axioms ' + r + '\n' for r in requests).encode()
    new[HARNESS] = imports + old[HARNESS] + prints
    external = set()
    for data in sources.values():
        external.update(m for m in re.findall(r'^import (\S+)', data.decode(), re.M) if not m.startswith('PvNP.'))
    manifest['external_imports'] += sorted(external - set(manifest['external_imports']))
    for module in external:
        assert module.startswith('Mathlib.')
        pinpath = '.lake/packages/mathlib/' + module.replace('.', '/') + '.lean'
        assert pinpath in manifest['cache_provenance']['package_sources'], 'Unpinned external import: ' + module
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    validate_expansion(old, new)
    return new


def validate_expansion(old, new):
    sources, requests = additions()
    assert set(new) == set(old) | set(sources)
    assert sorted(p for p in old if old[p] != new[p]) == sorted([HARNESS, 'capture-manifest.json'])
    a, b = json.loads(old['capture-manifest.json']), json.loads(new['capture-manifest.json'])
    assert len(a['project_sources']) == 327 and len(b['project_sources']) == 340
    assert len(a['requested_axioms']) == 192 and b['requested_axioms'] == a['requested_axioms'] + requests
    assert len(set(b['requested_axioms'])) == 251 and len(b['stages']) == 7
    assert b['owned_sources'] == a['owned_sources'] + list(sources)
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    for i in range(7):
        suffix = [m for m in modules if not m.endswith('Checks')] if i == 4 else [m for m in modules if m.endswith('Checks')] if i == 5 else []
        assert b['stages'][i] == dict(a['stages'][i], argv=a['stages'][i]['argv'] + suffix)
    assert new[HARNESS] == ''.join('import ' + m + '\n' for m in modules).encode() + old[HARNESS] + ''.join('#print axioms ' + r + '\n' for r in requests).encode()
    normalized = copy.deepcopy(b)
    for rel, data in sources.items():
        assert new[rel] == data and b['project_sources'][rel] == dict(sha256=sha(data), bytes=len(data))
        normalized['project_sources'].pop(rel)
    for field in ['owned_sources', 'requested_axioms', 'stages', 'external_imports']:
        normalized[field] = a[field]
    assert normalized == a, 'Compiler/package/core/cache/configuration or original statement context changed'
    added_external = {m for data in sources.values() for m in re.findall(r'^import (\S+)', data.decode(), re.M)
                      if not m.startswith('PvNP.')}
    assert b['external_imports'] == a['external_imports'] + sorted(added_external - set(a['external_imports']))
    allmodules = {p.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): p for p in b['project_sources']}
    pending = re.findall(r'^import (\S+)', new[HARNESS].decode(), re.M)
    reached = set()
    while pending:
        module = pending.pop()
        if module in reached or module not in allmodules:
            assert module in reached or not module.startswith('PvNP.'), 'Missing project import: ' + module
            continue
        reached.add(module)
        pending += re.findall(r'^import (\S+)', new[allmodules[module]].decode(), re.M)
    assert reached == set(allmodules), 'Entire340-project-source graph must remain reachable'
    return True


def parent_custody():
    marker = read(PARENT / 'launch-once.json')
    check = Path(marker['preflight'])
    terminal = read(check / 'terminal-custody.json')
    stop = read(check / 'vm-termination.json')
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '66BFF34BC77A2A558BB06EDC6FE9382A2A8210804C56C9499F37218E102E8475'
    assert marker['run'] == terminal['run'] == stop['run'] and terminal['terminal']['compile_green']
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == '7237681467779354904'
    report = check / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    qualified = read(report)
    assert digest(report) == '4D580EA63CF139E497FF366D007B5E8FB94B2AB9C6DB0DCE1FFF67D34A1883A4'
    assert qualified['full100_expanded_native_gates_green'] and qualified['all_seven_stage_exits'] == [0] * 7
    q = PARENT / 'consumption-v2/qualification/qualification-summary.json'
    assert digest(q) == '081C0CA1B30A1B3EC76E1BFB79980ED228EEFE769546468C3BFB7140769CAF60'
    assert read(q)['structural_trace_qualification']
    trace_marker = read(PARENT / 'consumption-v2/launch-once.json')
    trace_check = Path(trace_marker['preflight'])
    tc = read(trace_check / 'terminal-custody.json')['custody']
    verify_local_custody(tc['short_path'], tc['repository_path'], tc['remote_sha256'], tc['bytes'])
    assert tc['remote_sha256'] == 'BB5288CAC22AE2336F010B1B14EE27B40808222223B224E1D45D78ED26C09DE1'
    ts = read(trace_check / 'vm-termination.json')
    assert ts['independent']['status'] == 'TERMINATED' and str(ts['independent']['id']) == '7237681467779354904'
    reviews = []
    for folder in ['full100-material-integration-reports', 'full100-identity-addendum-reports']:
        for lens in ['proof-adversarial', 'complexity', 'non-claims']:
            p = HERE / folder / (lens + '-01.md')
            receipt = read(p.with_suffix('.json'))
            assert digest(p) == receipt['report_sha256'] and receipt['native_exit'] == 0 and receipt['actual_packet_context_fit']
            reviews.append(dict(path=str(p), report_sha256=digest(p), receipt_sha256=digest(p.with_suffix('.json'))))
    return marker, custody, report, q, reviews


def main():
    from full100_capture_gates import validate_successor
    validate_successor()
    marker, custody, report, q, reviews = parent_custody()
    binding = read(PARENT / 'resource-binding.json')
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = make_successor(old)
    sources, requests = additions()
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(schema='full101-full340-full251-original-spectral-application-v1', parent_run=marker['run'],
        parent_custody=custody, parent_qualified_report_sha256=digest(report), parent_trace_qualification_sha256=digest(q),
        six_parent_reviews=reviews, conditional_parent_verdict='GO-WITH-NOTES; all broader debt retained',
        repaired_sources=[], added_sources=list(sources), additional_profiles=requests,
        all327_parent_source_bytes_preserved=True, all192_parent_profiles_preserved=True,
        all_seven_parent_stage_commands_preserved_as_prefixes=True, entire340_source_graph_reachable=True,
        compiler_packages_core_cache_configs_preserved=True, all13_new_sources_in_owned_warning_scope=True,
        recovered_candidate_receipt_sha256=digest(RECOVERED / 'recovery.json'),
        application_derivation_sha256=digest(CANDIDATES / 'derivation.json'),
        manuscript_exact_eigenvalue_and_G_Phi_laws_remain_open=True,
        surplus_object_provenance_and_sidecar_debt_retained=True, R14='HIGH open',
        compiler_invoked=False, native_verification_pending=True, launch_clearance=False, accepted=False, full_goal_complete=False)
    (OUTPUT / 'source-expansion.json').write_bytes((json.dumps(expansion, indent=2) + '\n').encode())
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'), changed_files=[HARNESS, 'capture-manifest.json'],
        added_files=list(sources), project_sources_preserved=327, additional_profiles=requests,
        auxiliary_inputs={n: sha(new[n]) for n in binding['auxiliary_inputs']},
        files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    (OUTPUT / 'resource-binding.json').write_bytes((json.dumps(successor, indent=2) + '\n').encode())
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=340, profiles=251, input_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
                         manifest_sha256=digest(OUTPUT / 'capture-manifest.json'), launch_clearance=False)))


if __name__ == '__main__':
    main()
