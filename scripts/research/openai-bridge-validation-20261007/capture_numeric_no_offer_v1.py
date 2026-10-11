"""Freeze the full numeric-NO offer, including static defects, before routine author repair."""
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'actual-numeric-no-candidate-v1'
    manifest = source / 'OFFER-MANIFEST.json'
    assert digest(manifest) == '286BE5EE765B561FE70D412D8D1C13DCFE6AC7000DE664C2F6C82E84FA97C673'
    rows = json.loads(manifest.read_bytes())['files']
    rows.append(dict(path=manifest.name, bytes=manifest.stat().st_size, sha256=digest(manifest)))
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows}
    lexical, contents = [], {}
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256'].upper()
        data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf')
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    archive_path = Path('C:/Users/dfred/.quantyra/builder02/full110-exact-real-complex-operators-resource02/input-archive.tar.gz')
    assert digest(archive_path) == 'C1702903ECC5F939B9504371D63F0D4313E192446971EF0DD7627F6E770F3C61'
    dependencies = {
        'ActualMaximalPairLadder.lean': 'D61DF4001A90D5F5CF56B756151212F2EC1DDC8E10A64D919F0E046993E3FA81',
        'ActualBinaryMatrixHC46FourierA16.lean': '21E062E1FE12023D981810AF3C06A9D463F25FB568B6ECF10F8B3396CD16A045',
        'ActualSelectedComplementSourceSizeAnalyticMoment.lean': '03FB0A5DE3FD2E7E150645825165D2E30CFCE60BD34765BF7D6623E3A6D2D3D1',
    }
    with tarfile.open(archive_path) as archive:
        for name, pin in dependencies.items():
            data = archive.extractfile('lean/PvNP/RealizableHardness/'+name).read()
            assert hashlib.sha256(data).hexdigest().upper() == pin
    target = HERE / 'numeric-no-offer-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == (source / name).read_bytes()
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    result = dict(original_directory=str(source), files=rows, lexical_preflight=lexical,
        dependencies=dependencies, dependency_archive_sha256=digest(archive_path),
        root_read_all_four_files=True, immutable_capture_acknowledged=True,
        static_findings=[
            'Main namespace is ActualNumericNoCandidate but Checks requests ActualNumericNo; align exact public declaration names.',
            'submoduleCode/submoduleCode_injective/submodule_finite/vector_subtype_finite/dual_finite lack the AddCommGroup and Module instances required by Submodule and dual map types.',
            'indicator_mean_le_one writes a forall binder with Real body where the sum of constant ones is required; replace with the intended finite sum.',
            'booleanRankEnergy_total_le_one is private but requested by a public qualified name in Checks; expose the intended public total bound.',
            'ARGUMENT-MAP.md has lost glyphs (q?r, V ? Bool, comparison and type arrows); repair prose explicitly without changing mathematical scope.'
        ],
        honest_scope='Complete same-table finite maximum, Boolean total energy and weighted tail under explicit integer ambient bound; no numeric-NO conclusion or selected witness.',
        lean_executed=False, native_verified=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), files=len(rows), static_findings=len(result['static_findings']),
                         capture_index_sha256=digest(target / 'index.json'), native_verified=False)))


if __name__ == '__main__':
    main()
