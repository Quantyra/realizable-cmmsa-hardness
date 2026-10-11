"""Check the eleven captured numeric, density, inverse, robust arithmetic and fixed-frame offers as an additive proposal; no Lean or cloud work."""
import copy
import hashlib
import json
from pathlib import Path
import re
import tarfile
from lean_source_static_preflight_v1 import code_only
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import declarations, imports

HERE = Path(__file__).resolve().parent
PARENT = Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02')
INPUT_SHA = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
MANIFEST_SHA = '60DE0615C4B5228F0AFE9A9D2DB487D92866C811D2E7595A06AA63CB18ED243E'
PREFIX = 'lean/PvNP/RealizableHardness/'
HARNESS = 'fresh-integrated-axioms.lean'
CAPTURES = [
    ('numeric-no-offer-capture-v2', '83364D846210E4D0460E968B80395EF6F1F9363F23486D27A21C230E1C16B54D'),
    ('numeric-source-height-offer-capture-v3', '7CD8C1D6463A39ECDE018F278360847F6874C3F8A2A3CB57FFC2D687B025C96D'),
    ('numeric-scalar-offer-capture-v6', '3EB1E16820BE3B30BF51C39907ADFFF443A4E03D178D5B6B840F61F98BDACBC9'),
    ('numeric-explicit-height-offer-capture-v3', '48323F05192D57BC7E308FD80CF15CBA2ABA0DAF474DF603C9A49F09FB9D5B3F'),
    ('actual-global-density-bridge-capture-v2', '30A2513548AC7DC5AB2521977D60BCCC05D5AA5EC4C23DA224D55CDE3B0C079A'),
    ('numeric-exact-threshold-capture-v2', 'EFEC33817B3F7585E51AD5DA03840F8566E7C3FF61DA5FE8F0E30C3A21C62C22'),
    ('numeric-same-instance-composition-capture-v3', '7499538C6B2BE856EB26C4D4F2B8B2F48844FFB26E64ED93089D1E0F518C19F1'),
    ('numeric-physical-density-capture-v4', 'E010176FB8A1353D70923DA51198ED457FE3DF51B3909B8A6E260CF713076B91'),
    ('numeric-fixed-coordinate-inverse-capture-v3', 'EB080E7153B58F1E286358C7B46257C0BE85C1722E2C094939585287ACA7B17C'),
    ('numeric-robust-cutoffs-capture-v1', 'E1211C7F55353E7627026CB21A63E234971E724D07461EA5153066AFC3345139'),
    ('numeric-fixed-frame-transport-capture-v2', '846038D54E7E6B8A8C75D5D91102756888D09C5D67E90FBA7F2C314562990A44'),
]


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def additions():
    sources, provenance = {}, []
    for folder, pin in CAPTURES:
        raw = (HERE / folder / 'index.json').read_bytes()
        assert sha(raw) == pin, 'Capture index changed: ' + folder
        index = json.loads(raw)
        for row in index['files']:
            data = (HERE / folder / row.get('path',row.get('copy'))).read_bytes()
            assert len(data) == row['bytes'] and sha(data) == row['sha256']
            if not row.get('path',row.get('copy')).endswith('.lean'):
                continue
            inspect_bytes(data, folder + '/' + row.get('path',row.get('copy')))
            rel = PREFIX + row.get('path',row.get('copy'))
            assert rel not in sources
            sources[rel] = data
            provenance.append(dict(capture=folder, capture_index_sha256=pin,
                                   path=rel, bytes=len(data), sha256=sha(data)))
    assert len(sources) == 22
    requests, explicit = [], []
    for rel, data in sources.items():
        if rel.endswith('Checks.lean'):
            explicit += re.findall(r'(?m)^#print axioms\s+(\S+)', code_only(data.decode('utf-8')))
        else:
            requests += declarations(data)
    assert len(requests) == len(set(requests))
    requests += [r for r in dict.fromkeys(explicit) if r not in requests]
    assert set(explicit) <= set(requests) and len(requests) == 50
    return sources, requests, provenance


def parent():
    path = PARENT / 'input-archive.tar.gz'
    assert sha(path.read_bytes()) == INPUT_SHA
    with tarfile.open(path, 'r:gz') as archive:
        members = archive.getmembers()
        assert all(m.isfile() for m in members)
        assert len(members) == len({m.name for m in members}) == 376
        old = {m.name: archive.extractfile(m).read() for m in members}
    assert sha(old['capture-manifest.json']) == MANIFEST_SHA
    assert old['capture-manifest.json'] == (PARENT / 'capture-manifest.json').read_bytes()
    manifest = json.loads(old['capture-manifest.json'])
    assert len(manifest['project_sources']) == 369 and len(manifest['requested_axioms']) == 347
    assert len(manifest['stages']) == 7
    for rel, row in manifest['project_sources'].items():
        assert len(old[rel]) == row['bytes'] and sha(old[rel]) == row['sha256']
    return old


def make_successor(old):
    sources, requests, _ = additions()
    new = dict(old)
    assert not set(sources) & set(old)
    new.update(sources)
    manifest = json.loads(old['capture-manifest.json'])
    assert not set(requests) & set(manifest['requested_axioms'])
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
    assert len(b['project_sources']) == 391 and len(b['requested_axioms']) == 397
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
    assert normalized == a, 'Parent source, package, compiler, cache or configuration drift'
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
            assert not module.startswith('PvNP.'), 'Missing project dependency: ' + module
            continue
        reached.add(module)
        pending += imports(new[all_modules[module]])
    assert reached == set(all_modules)
    return True


def negative_checks(old, new):
    sources, _, _ = additions()
    results = []
    for name in ('parent_bytes', 'missing_parent', 'candidate_bytes', 'missing_candidate',
                 'profile_dropped', 'stage_dropped', 'warm_cache_changed', 'external_import_dropped',
                 'owned_source_dropped', 'harness_changed'):
        bad = dict(new)
        manifest = json.loads(new['capture-manifest.json'])
        rel = next(iter(json.loads(old['capture-manifest.json'])['project_sources']))
        if name == 'parent_bytes': bad[rel] += b'\n'
        elif name == 'missing_parent': bad.pop(rel)
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
    result = dict(schema='complete-numeric-additive-scope-proposal-v6',
        parent_input_sha256=INPUT_SHA, parent_manifest_sha256=MANIFEST_SHA,
        parent_native_status='Full114 failed with one GL source error; independently stopped; unchanged audit failed; not accepted',
        project_sources=391, requested_profiles=397, additional_requests=requests,
        exact_candidate_sources=provenance, negative_scope_checks=negative_checks(old, new),
        unchanged369_sources347_requests_seven_stage_prefixes_preserved=True,
        all_public_candidate_theorems_and_explicit_axiom_requests_included=True,
        entire_project_import_graph_reachable=True,
        generated_manifest_sha256=sha(new['capture-manifest.json']),
        generated_harness_sha256=sha(new[HARNESS]),
        execution_archive_created=False, cloud_operation=False, lean_executed=False,
        requires_rebind_to_actual_accepted_operator_successor_before_execution=True,
        fixed_frame_v2_all12_public_requests_added=True,
        native_verified=False, accepted=False, full_goal_complete=False,
        remaining=['Native/axiom/warning verification and consumption/body review',
                   'GCP-verify same-instance and fixed-coordinate Real inverse candidates and the physical same-witness row-validity consequence',
                   'Fixed-frame transport, robust refresh preservation and many-Q amplification with explicit cutoffs; same-law decoder and SAT-derived source NO promise; retain eligible-U mass',
                   'Effective source base and encoded runtime; spectral cutoff zero specialization already source-supported'])
    path = HERE / 'complete-numeric-additive-scope-proposal-v6.json'
    path.open('x', encoding='utf-8', newline='\n').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(sources=391, profiles=397, additional_profiles=len(requests),
                         negative_checks=len(result['negative_scope_checks']),
                         sha256=sha(path.read_bytes()), compiler_invoked=False)), flush=True)


if __name__ == '__main__':
    main()
