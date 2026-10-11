"""Prepare and adversarially check a full-scope real/complex operator and Gram successor; never execute Lean."""
import copy
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile
from lean_source_static_preflight_v1 import code_only
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PARENT = Path('C:/Users/dfred/.quantyra/builder02/full109-exact-crosslevel-warning-repair-resource02')
INPUT_SHA = 'F5C8D78779B0ABE00A21DE9C960719B0BC6CE6978AA97382F699F0EC519593EC'
MANIFEST_SHA = '7212F8D1D98A899BA54DC3498D3E47CC3B68AAB432B3BA3B68ABA74117B8E6B4'
QUALIFIED_SHA = '467EB67622142D6B1A959F4C7D20510B6A785D430BB91C6D9F0435F20D5FECA4'
HARNESS = 'fresh-integrated-axioms.lean'
PREFIX = 'lean/PvNP/RealizableHardness/'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def imports(data):
    return re.findall(r'(?m)^import\s+(\S+)', code_only(data.decode('utf-8')))


def declarations(data):
    code = code_only(data.decode('utf-8'))
    namespaces = re.findall(r'(?m)^namespace\s+(\S+)', code)
    assert len(namespaces) == 1, 'Review nested or missing namespace explicitly'
    # Include inline attributes; exclude private declarations. Do not inspect comments.
    names = re.findall(r'(?m)^(?:@\[[^\]\n]+\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+([\w\u0080-\uffff\']+)', code)
    return [namespaces[0] + '.' + name for name in names]


def additions():
    sources, provenance = {}, []
    for directory, field, pin in [('operator-complete-offer-capture-v3', 'path', '3D892EAA6A8BF5103F4C697FCB862287A69D51BD32301575B0B37E2013E38173'), ('phi-eigenrelation-offer-capture-v4', 'copy', '3423358517781BCA5AD6220B131216293B9D3E19DC61A84F2D67D21AB09EB056'), ('real-gram-offer-capture-v1', 'path', '169D5BF3439215ACFA83B24D7A42DF0E398C53A5AF352B88FB0EC3202B49AA65'), ('complex-operator-complete-offer-capture-v4', 'path', 'DB7B77C3618AB6E94ECD761FAA7117810B7B56EB454B552DD4B74FA966AF3683'), ('complex-gram-offer-capture-v2', 'path', '81DE316ECEFC4DBD34744933566FFB93221857A7AF2128D92842A2BC805EEE24')]:
        index_bytes = (HERE / directory / 'index.json').read_bytes()
        assert sha(index_bytes) == pin, 'Immutable capture index changed: ' + directory
        index = json.loads(index_bytes)
        for row in index['files']:
            name = row[field]
            if not name.endswith('.lean'):
                continue
            data = (HERE / directory / name).read_bytes()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
            inspect_bytes(data, directory + '/' + name)
            canonical = name.replace('-v4.lean', '.lean')
            rel = PREFIX + canonical
            assert rel not in sources
            sources[rel] = data
            provenance.append(dict(original=directory + '/' + name, canonical=rel,
                                   bytes=len(data), sha256=sha(data)))
    assert len(sources) == 21
    requests, explicit = [], []
    for rel, data in sources.items():
        if rel.endswith('Checks.lean'):
            explicit += re.findall(r'(?m)^#print axioms\s+(\S+)', code_only(data.decode('utf-8')))
        else:
            requests += declarations(data)
    assert len(requests) == len(set(requests)), 'Duplicate public theorem'
    # Some Checks also expose finite-equivalence definitions. Preserve them too.
    requests += [name for name in dict.fromkeys(explicit) if name not in requests]
    assert set(explicit) <= set(requests)
    assert 'PvNP.RealizableHardness.ExactRestrictedAdjoint.firstBlock_append' in requests
    assert 'PvNP.RealizableHardness.ExactRestrictedAdjoint.firstBlock_mul' in requests
    return sources, requests, provenance


def parent():
    data = (PARENT / 'input-archive.tar.gz').read_bytes()
    assert sha(data) == INPUT_SHA
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as archive:
        members = archive.getmembers()
        assert all(m.isfile() for m in members)
        assert len({m.name for m in members}) == len(members)
        old = {m.name: archive.extractfile(m).read() for m in members}
    assert sha(old['capture-manifest.json']) == MANIFEST_SHA
    assert old['capture-manifest.json'] == (PARENT / 'capture-manifest.json').read_bytes()
    manifest = json.loads(old['capture-manifest.json'])
    assert len(manifest['project_sources']) == 348 and len(manifest['requested_axioms']) == 261
    assert len(manifest['stages']) == 7
    for rel, row in manifest['project_sources'].items():
        assert len(old[rel]) == row['bytes'] and sha(old[rel]) == row['sha256']
    evidence = (HERE / 'full109-qualified-native-record-v1/036-material-expanded-native-report.json').read_bytes()
    assert sha(evidence) == QUALIFIED_SHA
    report = json.loads(evidence)
    assert report['full109_expanded_native_gates_green']
    assert report['all_seven_stage_exits'] == [0] * 7
    assert report['project_closure_sources'] == 348
    assert report['owned_warning_headers'] == report['inherited_regression_headers'] == [0] * 7
    assert report['accepted'] is False
    return old


def make_successor(old):
    sources, requests, _ = additions()
    manifest = json.loads(old['capture-manifest.json'])
    assert not set(sources) & set(old)
    assert not set(requests) & set(manifest['requested_axioms'])
    new = dict(old)
    new.update(sources)
    for rel, data in sources.items():
        manifest['project_sources'][rel] = dict(bytes=len(data), sha256=sha(data))
    manifest['owned_sources'] += list(sources)
    manifest['requested_axioms'] += requests
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    manifest['stages'][4]['argv'] += [m for m in modules if not m.endswith('Checks')]
    manifest['stages'][5]['argv'] += [m for m in modules if m.endswith('Checks')]
    external = {m for data in sources.values() for m in imports(data) if not m.startswith('PvNP.')}
    manifest['external_imports'] += sorted(external - set(manifest['external_imports']))
    new[HARNESS] = (''.join('import ' + m + '\n' for m in modules).encode() + old[HARNESS] +
                    ''.join('#print axioms ' + r + '\n' for r in requests).encode())
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    validate(old, new)
    return new


def validate(old, new):
    sources, requests, _ = additions()
    a, b = [json.loads(x['capture-manifest.json']) for x in (old, new)]
    assert set(new) == set(old) | set(sources)
    assert {p for p in old if old[p] != new[p]} == {HARNESS, 'capture-manifest.json'}
    assert len(b['project_sources']) == 369
    assert b['requested_axioms'] == a['requested_axioms'] + requests
    assert b['owned_sources'] == a['owned_sources'] + list(sources)
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    assert len(b['stages']) == 7
    for i in range(7):
        suffix = ([m for m in modules if not m.endswith('Checks')] if i == 4 else
                  [m for m in modules if m.endswith('Checks')] if i == 5 else [])
        assert b['stages'][i] == dict(a['stages'][i], argv=a['stages'][i]['argv'] + suffix)
    assert new[HARNESS] == (''.join('import ' + m + '\n' for m in modules).encode() + old[HARNESS] +
                            ''.join('#print axioms ' + r + '\n' for r in requests).encode())
    normalized = copy.deepcopy(b)
    for rel, data in sources.items():
        assert new[rel] == data
        assert b['project_sources'][rel] == dict(bytes=len(data), sha256=sha(data))
        normalized['project_sources'].pop(rel)
    for field in ('requested_axioms', 'owned_sources', 'stages', 'external_imports'):
        normalized[field] = a[field]
    assert normalized == a, 'Compiler/package/core/warm-cache/configuration or parent scope drift'
    external = {m for data in sources.values() for m in imports(data) if not m.startswith('PvNP.')}
    assert b['external_imports'] == a['external_imports'] + sorted(external - set(a['external_imports']))
    for module in external:
        assert module.startswith('Mathlib.')
        assert '.lake/packages/mathlib/' + module.replace('.', '/') + '.lean' in b['cache_provenance']['package_sources']
    all_modules = {p.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): p for p in b['project_sources']}
    pending, reached = imports(new[HARNESS]), set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        if module not in all_modules:
            assert not module.startswith('PvNP.'), 'Missing project import: ' + module
            continue
        reached.add(module)
        pending += imports(new[all_modules[module]])
    assert reached == set(all_modules)
    return True


def negative_checks(old, new):
    sources, _, _ = additions()
    parent_rel = next(iter(json.loads(old['capture-manifest.json'])['project_sources']))
    results = []
    for name in ('parent_bytes', 'missing_parent', 'candidate_bytes', 'missing_candidate',
                 'profile_dropped', 'stage_dropped', 'warm_cache_changed', 'external_import_dropped',
                 'owned_source_dropped', 'harness_changed'):
        bad = dict(new)
        manifest = json.loads(new['capture-manifest.json'])
        if name == 'parent_bytes': bad[parent_rel] += b'\n'
        elif name == 'missing_parent': bad.pop(parent_rel)
        elif name == 'candidate_bytes': bad[next(iter(sources))] += b'\n'
        elif name == 'missing_candidate': bad.pop(next(iter(sources)))
        elif name == 'profile_dropped': manifest['requested_axioms'].pop()
        elif name == 'stage_dropped': manifest['stages'].pop()
        elif name == 'warm_cache_changed': manifest['cache_provenance'] = {}
        elif name == 'external_import_dropped': manifest['external_imports'].pop()
        elif name == 'owned_source_dropped': manifest['owned_sources'].pop()
        elif name == 'harness_changed': bad[HARNESS] += b'\n'
        bad['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
        try:
            validate(old, bad)
        except (AssertionError, KeyError):
            results.append(dict(mutation=name, rejected=True))
        else:
            raise AssertionError('Mutation accepted: ' + name)
    return results


def main():
    old = parent()
    new = make_successor(old)
    sources, requests, provenance = additions()
    manifest = json.loads(new['capture-manifest.json'])
    result = dict(schema='complete-real-complex-operator-full-scope-proposal-v2',
                  parent_input_sha256=INPUT_SHA, parent_manifest_sha256=MANIFEST_SHA,
                  parent_qualified_native_report_sha256=QUALIFIED_SHA,
                  project_sources=len(manifest['project_sources']), requested_profiles=len(manifest['requested_axioms']),
                  additional_requests=requests, exact_candidate_sources=provenance,
                  lexical_only_preflight_passed=True,
                  original348_sources_261_profiles_seven_stage_prefixes_preserved=True,
                  entire_project_import_graph_reachable=True,
                  compiler_package_core_warm_cache_configuration_unchanged=True,
                  generated_manifest_sha256=sha(new['capture-manifest.json']),
                  generated_harness_sha256=sha(new[HARNESS]), negative_scope_checks=negative_checks(old, new),
                  parent_trace_and_independent_crosslevel_review_pending=True,
                  exact_real_complex_operator_and_two_function_gram_source_offers=True,
                  whole_complex_hypercontractivity_appendix_not_certified=True,
                  execution_archive_created=False, cloud_operation=False, lean_executed=False,
                  native_verified=False, accepted=False, full_goal_complete=False)
    target = HERE / 'complete-real-complex-operator-full-scope-proposal-v2.json'
    data = (json.dumps(result, indent=2) + '\n').encode()
    if target.exists():
        assert target.read_bytes() == data
    else:
        target.open('xb').write(data)
    print(json.dumps(dict(sources=result['project_sources'], profiles=result['requested_profiles'],
                          additional_profiles=len(requests), negative_checks=len(result['negative_scope_checks']),
                          sha256=sha(data), execution_archive_created=False, native_verified=False)))


if __name__ == '__main__':
    main()
