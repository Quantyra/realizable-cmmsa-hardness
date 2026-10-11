"""Preserve a rejected static offer without altering it or running Lean."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
MANIFEST = '9D232267CE3283B3F48D4BCC1864B95A5EA49775A6AB680C2AF76374E7742B57'
HEIGHT_INDEX = '48323F05192D57BC7E308FD80CF15CBA2ABA0DAF474DF603C9A49F09FB9D5B3F'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-physical-density-offer-v1'
    raw = (offer / 'manifest.json').read_bytes()
    assert sha(raw) == MANIFEST
    value = json.loads(raw)
    assert {p.name for p in offer.iterdir()} == {'manifest.json'} | {r['file'] for r in value['offered_files']}
    for row in value['offered_files']:
        data = (offer / row['file']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    inp = value['input']['full114_input_archive']
    archive = Path(inp['path'])
    assert sha(archive.read_bytes()) == inp['sha256']
    dependencies = []
    additional = ['ActualTaggedConcreteStarLaw', 'ActualTaggedFixedTableAcceptance',
                  'ActualTaggedPresentedSelection', 'ActualFiniteLaw',
                  'ActualCmmsaAdmissibilitySelector', 'ActualCmmsaParameterReconciliation']
    with tarfile.open(archive, 'r:gz') as tar:
        manifest = json.load(tar.extractfile('capture-manifest.json'))
        for row in value['project_dependencies'] + [value['input']['lake_manifest'], value['input']['lean_toolchain']]:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
            dependencies.append(dict(row, verified=True))
        for name in additional:
            member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
            data = tar.extractfile(member).read()
            assert manifest['project_sources'][member]['bytes'] == len(data) and manifest['project_sources'][member]['sha256'] == sha(data)
            dependencies.append(dict(member=member, bytes=len(data), sha256=sha(data), verified=True))
    numeric, mismatches = [], []
    for row in value['captured_numeric_dependencies']:
        folder = HERE / row['capture']
        data = (folder / 'index.json').read_bytes()
        actual = sha(data)
        if actual != row['capture_index_sha256']:
            assert row['module'] == 'ActualNumericExplicitHeight' and actual == HEIGHT_INDEX
            mismatches.append(dict(module=row['module'], offered=row['capture_index_sha256'], actual=actual))
        index = json.loads(data)
        for item in index['files']:
            content = (folder / item.get('copy', item.get('path'))).read_bytes()
            assert len(content) == item['bytes'] and sha(content) == item['sha256']
        assert sha((folder / (row['module'] + '.lean')).read_bytes()) == row['source_sha256']
        numeric.append(dict(row, verified_actual_index_sha256=actual))
    assert len(mismatches) == 1
    source = offer / 'ActualNumericPhysicalDensity.lean'
    checks = offer / 'ActualNumericPhysicalDensityChecks.lean'
    lexical = [inspect_bytes(p.read_bytes(), p.name) for p in (source, checks)]
    declarations = re.findall(r'(?m)^theorem (\w+)', source.read_text(encoding='utf-8'))
    requests = re.findall(r'(?m)^#print axioms (.+)$', checks.read_text(encoding='utf-8'))
    assert requests == value['requested_axioms']
    assert set(requests) == {'PvNP.RealizableHardness.ActualNumericPhysicalDensity.' + n for n in declarations}
    target = HERE / 'numeric-physical-density-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for path in sorted(offer.iterdir()):
        data = path.read_bytes()
        (target / path.name).open('xb').write(data)
        assert (target / path.name).read_bytes() == data
        rows.append(dict(original=str(path), copy=path.name, bytes=len(data), sha256=sha(data)))
    report = dict(files=rows, project_dependencies=dependencies,
        numeric_dependencies=numeric, manifest_discrepancies=mismatches,
        lexical_preflight=lexical, requested_axioms=requests,
        root_read_complete_source_checks_map_manifest=True,
        static_review_concerns=[
            'Manifest has stale explicit-height capture-index hash; actual capture source hash matches.',
            'Unqualified carrier/table/mass names require opens or qualification for ActualTaggedConcreteStarLaw, ActualTaggedFixedTableAcceptance, ActualTaggedPresentedSelection and ActualFiniteLaw.'
        ],
        argument_alignment='Original strict physical-score premise and full 8*S eligible-U mass retained; source rows independent of selected star count.',
        repair_requested=True, compiler_invoked=False, accepted=False,
        capture_control_sha256=sha(Path(__file__).read_bytes()))
    out = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(out)
    print(json.dumps(dict(folder=target.name, index_sha256=sha(out), requests=len(requests), uncompiled=True)))


if __name__ == '__main__':
    main()
