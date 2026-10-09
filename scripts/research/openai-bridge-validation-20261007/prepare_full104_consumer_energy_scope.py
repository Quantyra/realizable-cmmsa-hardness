"""Prepare full-scope actual-consumer/exact-energy addition, without execution."""
import copy
import json
import re
from pathlib import Path
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full103 import OUTPUT as PARENT

HERE = Path(__file__).parent
HARNESS = 'fresh-integrated-axioms.lean'
CANDIDATES = [('sourcesize-spectral-application-candidate-v2','derivation.json'),
              ('spectral-exact-energy-candidate-v1','candidate.json')]


def additions():
    sources = {}; requests = []
    for folder, record in CANDIDATES:
        root = HERE/folder
        rows = json.loads((root/record).read_bytes())['files']
        for row in rows:
            data = (root/Path(row['path']).name).read_bytes()
            assert sha(data) == row['sha256'] and len(data) == row['bytes']
            text = data.decode('utf-8')
            assert not data.startswith(b'\xef\xbb\xbf')
            assert not re.search(r'^\s*-[ \t]+',text,re.M)
            assert not re.search(r'\b(?:sorry|admit|axiom)\b',text)
            assert row['path'] not in sources
            sources[row['path']] = data
            if row['path'].endswith('Checks.lean'): continue
            namespace = re.search(r'(?m)^namespace (\S+)',text).group(1)
            requests.extend(namespace+'.'+name for name in re.findall(r'(?m)^theorem (\w+)',text))
    assert len(sources) == 4 and len(requests) == len(set(requests)) == 6
    return sources, requests


def make_successor(old):
    sources, requests = additions()
    new = dict(old); manifest = json.loads(old['capture-manifest.json'])
    assert len(manifest['project_sources']) == 340 and len(manifest['requested_axioms']) == 251
    assert not set(sources)&set(manifest['project_sources'])
    assert not set(requests)&set(manifest['requested_axioms'])
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/','.') for p in sources]
    new.update(sources)
    for rel,data in sources.items(): manifest['project_sources'][rel] = dict(sha256=sha(data),bytes=len(data))
    manifest['owned_sources'] += list(sources)
    manifest['requested_axioms'] += requests
    manifest['stages'][4]['argv'] += [m for m in modules if not m.endswith('Checks')]
    manifest['stages'][5]['argv'] += [m for m in modules if m.endswith('Checks')]
    new[HARNESS] = ''.join('import '+m+'\n' for m in modules).encode()+old[HARNESS]+''.join('#print axioms '+r+'\n' for r in requests).encode()
    external = {m for data in sources.values() for m in re.findall(r'^import (\S+)',data.decode(),re.M) if not m.startswith('PvNP.')}
    manifest['external_imports'] += sorted(external-set(manifest['external_imports']))
    for module in external:
        assert module.startswith('Mathlib.')
        assert '.lake/packages/mathlib/'+module.replace('.','/')+'.lean' in manifest['cache_provenance']['package_sources']
    new['capture-manifest.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    validate_expansion(old,new)
    return new


def validate_expansion(old,new):
    sources,requests = additions()
    assert set(new) == set(old)|set(sources)
    assert {p for p in old if old[p]!=new[p]} == {HARNESS,'capture-manifest.json'}
    a = json.loads(old['capture-manifest.json']); b = json.loads(new['capture-manifest.json'])
    assert len(b['project_sources']) == 344 and len(b['requested_axioms']) == 257 and len(b['stages']) == 7
    assert b['requested_axioms'] == a['requested_axioms']+requests
    assert b['owned_sources'] == a['owned_sources']+list(sources)
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/','.') for p in sources]
    for i in range(7):
        suffix = [m for m in modules if not m.endswith('Checks')] if i==4 else [m for m in modules if m.endswith('Checks')] if i==5 else []
        assert b['stages'][i] == dict(a['stages'][i],argv=a['stages'][i]['argv']+suffix)
    assert new[HARNESS] == ''.join('import '+m+'\n' for m in modules).encode()+old[HARNESS]+''.join('#print axioms '+r+'\n' for r in requests).encode()
    normalized = copy.deepcopy(b)
    for rel,data in sources.items():
        assert new[rel] == data and b['project_sources'][rel] == dict(sha256=sha(data),bytes=len(data))
        normalized['project_sources'].pop(rel)
    for field in ('requested_axioms','owned_sources','stages','external_imports'): normalized[field]=a[field]
    assert normalized == a
    external = {m for data in sources.values() for m in re.findall(r'^import (\S+)',data.decode(),re.M) if not m.startswith('PvNP.')}
    assert b['external_imports'] == a['external_imports']+sorted(external-set(a['external_imports']))
    allmodules = {p.removeprefix('lean/').removesuffix('.lean').replace('/','.'):p for p in b['project_sources']}
    pending = re.findall(r'^import (\S+)',new[HARNESS].decode(),re.M); reached=set()
    while pending:
        module=pending.pop()
        if module in reached: continue
        if module not in allmodules:
            assert not module.startswith('PvNP.'),'Missing project dependency: '+module
            continue
        reached.add(module);pending += re.findall(r'^import (\S+)',new[allmodules[module]].decode(),re.M)
    assert reached == set(allmodules)
    return True


def main():
    old=capsule(PARENT/'input-archive.tar.gz');new=make_successor(old)
    sources,requests=additions()
    result=dict(schema='full104-full344-full257-scope-proposal-v1',parent_manifest_sha256=digest(PARENT/'capture-manifest.json'),
        parent_input_sha256=digest(PARENT/'input-archive.tar.gz'),sources=344,requested_profiles=257,focused_consumers=89,
        candidate_sources={p:dict(sha256=sha(data),bytes=len(data)) for p,data in sources.items()},additional_requests=requests,
        parent340_source_bytes_and251_profiles_and_seven_stage_prefixes_preserved=True,entire344_source_graph_reachable=True,
        compiler_package_core_cache_configuration_unchanged=True,all_four_added_sources_owned=True,
        generated_manifest_sha256=sha(new['capture-manifest.json']),generated_harness_sha256=sha(new[HARNESS]),
        candidate_records={folder+'/'+record:digest(HERE/folder/record) for folder,record in CANDIDATES},
        exact_manuscript_s_factor_and_G_Phi_laws_closed=False,numeric_NO_proven=False,R14='HIGH open',
        immutable_capture_not_yet_created=True,parent_qualified_native_evidence_required=True,
        compiler_invoked=False,cloud_operation=False,native_verified=False,accepted=False)
    data=(json.dumps(result,indent=2)+'\n').encode();out=HERE/'full104-consumer-energy-scope-proposal-v1.json'
    if out.exists(): assert out.read_bytes()==data
    else:out.write_bytes(data)
    print(json.dumps(dict(sources=344,profiles=257,focused=89,entire_graph_reachable=True,
        scope_proposal_sha256=digest(out),immutable_capture_created=False,native_verified=False)))


if __name__=='__main__':main()
