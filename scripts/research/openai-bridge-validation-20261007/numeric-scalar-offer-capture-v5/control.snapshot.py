"""Capture the reviewed scalar v5 source candidate for future GCP diagnostics."""
import difflib
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def main():
    prior = HERE / 'numeric-scalar-offer-capture-v4'
    assert digest(prior / 'index.json') == 'EAFBA265074B4CE67C89086E7A4AC99CD889560F56C9535F0496F3DCEEA84EE3'
    old = json.loads((prior / 'index.json').read_bytes())
    for row in old['files']:
        assert digest(prior / row['path']) == row['sha256']
    source = HERE / 'actual-numeric-no-scalar-candidate-v5'
    assert digest(source / 'ActualNumericNoScalar.lean') == '8AE08AC67F689AA7A5CD5CFB91C42EDF735D73D5BAE7CB194E24B4624129DE43'
    assert digest(source / 'OFFER-MANIFEST.json') == '8A454DBE406C70E25F8D1B05D887ECB93A43E5840CB919C64C8B1D19D223888E'
    offered = json.loads((source / 'OFFER-MANIFEST.json').read_bytes())
    assert offered['dependencies'] == old['dependencies']
    archive_path = Path(offered['dependency_archive']['path'])
    assert digest(archive_path) == old['dependency_archive_sha256'] == offered['dependency_archive']['sha256']
    with tarfile.open(archive_path, 'r:gz') as archive:
        for row in offered['dependencies']:
            data = archive.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
    api = offered['mathlib_api_source']
    assert Path(api['path']).stat().st_size == api['bytes'] and digest(Path(api['path'])) == api['sha256']
    api_rows = []
    with tarfile.open(api['path'], 'r:gz') as archive:
        for name in api['read_only_inspected_members']:
            data = archive.extractfile(name).read()
            api_rows.append(dict(member=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    pins = {row['path']: row for row in offered['files']}
    assert len(pins) == len(offered['files']) == 3
    rows, contents, lexical = [], {}, []
    for path in sorted(source.iterdir()):
        assert path.is_file()
        data = path.read_bytes()
        assert not data.startswith(b'\xef\xbb\xbf')
        text = data.decode('utf-8')
        assert '?' not in text
        sha = hashlib.sha256(data).hexdigest().upper()
        if path.name != 'OFFER-MANIFEST.json':
            assert len(data) == pins[path.name]['bytes'] and sha == pins[path.name]['sha256']
        if path.suffix == '.lean':
            lexical.append(inspect_bytes(data, path.name))
        contents[path.name] = data
        rows.append(dict(path=path.name, bytes=len(data), sha256=sha))
    assert set(contents) == set(pins) | {'OFFER-MANIFEST.json'}
    target = HERE / 'numeric-scalar-offer-capture-v5'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == (source / name).read_bytes()
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    index = dict(original_directory=str(source), files=rows, lexical_preflight=lexical,
        prior_capture_index_sha256=digest(prior / 'index.json'), dependencies=offered['dependencies'],
        dependency_archive_sha256=digest(archive_path), mathlib_api_archive=api, mathlib_api_members=api_rows,
        complete_source_review_by_full_v4_and_exact_v5_diff=True, complete_checks_and_argument_map_read=True,
        complete_source_diff=''.join(difflib.unified_diff((prior / 'ActualNumericNoScalar.lean').read_text(encoding='utf-8').splitlines(True),
            contents['ActualNumericNoScalar.lean'].decode('utf-8').splitlines(True), fromfile='v4', tofile='v5')),
        preserved_stale_manifest_offer_label=offered['offer'], actual_offer_directory=source.name,
        stale_label_changes_no_source_identity=True, immutable_capture=True, development_candidate=True,
        routine_tactic_API_coercion_repairs_may_remain=True, compiler_invoked=False, native_verified=False,
        accepted=False, full_goal_complete=False,
        remaining=['GCP translation diagnostics and all native/axiom/review gates',
                   'Same-instance material/finite-maximum/parameter integration',
                   'Effective common cutoff, source/table/sampler and lower signal'])
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(index, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), index_sha256=digest(target / 'index.json'),
        exact_files=len(rows), development_candidate=True, native_verified=False)), flush=True)


if __name__ == '__main__':
    main()
