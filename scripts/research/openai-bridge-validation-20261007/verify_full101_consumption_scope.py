"""Verify all captured source imports and exact trace lists without compilation."""
import json
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full101 import OUTPUT


def main():
    root = OUTPUT / 'consumption-preparation-v1-dag'
    manifest = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    readiness = json.loads((root / 'readiness.json').read_bytes())
    spec = json.loads((root / 'preparation-status.json').read_bytes())
    probe = (root / 'probe.lean').read_text(encoding='utf-8')
    for name, row in readiness['files'].items():
        assert digest(root / name) == row['sha256'] and (root / name).stat().st_size == row['bytes']
    assert digest(root / 'tooling.tar.gz') == readiness['tooling_archive_sha256']
    modules = {p.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): row for p, row in manifest['project_sources'].items()}
    for field, expected in [('roots', manifest['requested_axioms']), ('projectModules', list(modules))]:
        match = re.search(r'private def ' + field + r' : List String := (\[.*?\])', probe)
        assert match and json.loads(match.group(1)) == expected
    assert spec['roots'] == manifest['requested_axioms'] and len(spec['roots']) == 251
    assert spec['focused_roots'] == readiness['focused_roots'] and len(set(spec['focused_roots'])) == 83
    with tarfile.open(OUTPUT / 'input-archive.tar.gz') as archive:
        imports = {}
        for rel, row in manifest['project_sources'].items():
            data = archive.extractfile(rel).read()
            assert sha(data) == row['sha256'] and len(data) == row['bytes']
            module = rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
            imports[module] = re.findall(r'^import (\S+)', data.decode(), re.M)
    todo = re.findall(r'^import (\S+)', probe, re.M)
    seen = set()
    while todo:
        module = todo.pop()
        if module in seen or module not in modules:
            assert module in seen or not module.startswith('PvNP.'), 'Uncaptured project import: ' + module
            continue
        seen.add(module)
        todo.extend(imports[module])
    assert seen == set(modules) and len(seen) == 340
    owners = {name: max((m for m in modules if name.startswith(m + '.')), key=len) for name in spec['roots']}
    assert set(owners.values()) <= seen
    report = dict(schema='full101-static-complete251-consumption-scope-v1',
        capture_manifest_sha256=digest(OUTPUT / 'capture-manifest.json'), tooling_archive_sha256=digest(root / 'tooling.tar.gz'),
        modules=340, roots=251, focused=83, imports_reach_every_captured_project_module=True,
        requested_owner_modules=owners, exact_probe_root_and_module_order=True,
        compiler_invoked=False, coverage_accepted=False)
    with (root / 'static-scope-audit.json').open('x', encoding='utf-8') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print('Exact Full101 probe scope verified:340 modules,251 roots,83 focused; no compilation')


if __name__ == '__main__':
    main()
