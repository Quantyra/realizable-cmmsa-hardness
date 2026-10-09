"""Static scope audit of pinned trace tooling; no Lean or GCP operation."""
import json
from pathlib import Path
import re
import tarfile
import hashlib
from custody_checks import digest
from prepare_builder02_full97 import OUTPUT

def main():
    root=OUTPUT/'consumption-preparation-v1-dag'
    manifest=json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    readiness=json.loads((root/'readiness.json').read_bytes())
    spec=json.loads((root/'preparation-status.json').read_bytes())
    probe=(root/'probe.lean').read_text(encoding='utf-8')
    for name,row in readiness['files'].items():
        assert digest(root/name)==row['sha256'] and (root/name).stat().st_size==row['bytes']
    assert digest(root/'tooling.tar.gz')==readiness['tooling_archive_sha256']
    modules={rel.removeprefix('lean/').removesuffix('.lean').replace('/','.'):row for rel,row in manifest['project_sources'].items()}
    for field,expected in [('roots',manifest['requested_axioms']),('projectModules',list(modules))]:
        match=re.search(r'private def '+field+r' : List String := (\[.*?\])',probe)
        assert match and json.loads(match.group(1))==expected
    assert spec['roots']==manifest['requested_axioms'] and len(spec['roots'])==184
    assert spec['focused_roots']==readiness['focused_roots'] and len(set(spec['focused_roots']))==16
    with tarfile.open(OUTPUT/'input-archive.tar.gz') as archive:
        imports={}
        for rel,row in manifest['project_sources'].items():
            data=archive.extractfile(rel).read()
            assert hashlib.sha256(data).hexdigest().upper()==row['sha256'] and len(data)==row['bytes']
            module=rel.removeprefix('lean/').removesuffix('.lean').replace('/','.')
            imports[module]=re.findall(r'^import (\S+)',data.decode(),re.M)
    todo=re.findall(r'^import (\S+)',probe,re.M);seen=set()
    while todo:
        module=todo.pop()
        if module in seen or module not in modules:continue
        seen.add(module);todo.extend(imports[module])
    assert seen==set(modules) and len(seen)==325
    owners={name:max((module for module in modules if name.startswith(module+'.')),key=len) for name in spec['roots']}
    assert set(owners.values())<=seen
    report=dict(schema='full97-static-complete184-consumption-scope-v1',capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
        tooling_archive_sha256=digest(root/'tooling.tar.gz'),modules=325,roots=184,focused=16,
        imports_reach_every_captured_project_module=True,requested_owner_modules=owners,
        exact_probe_root_and_module_order=True,compiler_invoked=False,coverage_accepted=False)
    with (root/'static-scope-audit.json').open('x',encoding='utf-8') as f:json.dump(report,f,indent=2);f.write('\n')
    print('Exact Full97 probe scope verified: 325 modules, 184 roots, 16 focused; no compilation')
if __name__=='__main__':main()
