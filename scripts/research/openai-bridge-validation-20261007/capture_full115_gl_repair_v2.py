"""Capture the uncompiled Full115 instance-transport offer without changing it."""
import difflib
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full114 import OUTPUT as PARENT
from lean_source_static_preflight_v2 import inspect_bytes
from full114_gl_repair_structure_v1 import declarations

HERE = Path(__file__).resolve().parent
OFFER = HERE / 'full115-rectangular-gl-repair-v2'
SOURCE = 'lean/PvNP/RealizableHardness/RectangularGLRowCompletion.lean'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    assert digest(OFFER / 'manifest.json') == '2BED011B1A7C220466C224DEB667EE8836CBFD67B468396C86BDB136874C6E84'
    manifest = json.loads((OFFER / 'manifest.json').read_bytes())
    assert digest(PARENT / 'input-archive.tar.gz') == manifest['input']['full114_input_archive']['sha256']
    packet = HERE / manifest['input']['diagnostic_packet']
    assert digest(packet / 'index.json') == manifest['input']['diagnostic_packet_index_sha256']
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    receipt = json.loads((Path(marker['preflight']) / 'terminal-custody.json').read_bytes())
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == 'F94CD8899B40E42802B5294EF4EFD0189F9584EBE8E1FAEABCC5826FED8A56A3'
    assert set(p.name for p in OFFER.iterdir()) == set(manifest['offered_files']) | {'manifest.json'}
    for name, row in manifest['offered_files'].items():
        assert (OFFER / name).stat().st_size == row['bytes'] and digest(OFFER / name) == row['sha256']
    with tarfile.open(PARENT / 'input-archive.tar.gz', 'r:gz') as archive:
        old = archive.extractfile(SOURCE).read()
        assert sha(old) == manifest['input']['input_source']['sha256']
        assert archive.extractfile(SOURCE.replace('.lean', 'Checks.lean')).read() == (OFFER / manifest['checks']['file']).read_bytes()
        for name, row in manifest['project_dependencies'].items():
            raw = archive.extractfile(name).read()
            assert len(raw) == row['bytes'] and sha(raw) == row['sha256']
        source_manifest = json.load(archive.extractfile('capture-manifest.json'))
    with tarfile.open(custody['repository_path'], 'r:gz') as native:
        raw_packages = native.extractfile('package-sources.tar.gz').read()
    assert sha(raw_packages) == manifest['external_dependencies'][0]['sha256']
    with tarfile.open(fileobj=io.BytesIO(raw_packages), mode='r:gz') as packages:
        row = manifest['external_dependencies'][1]
        member = '.lake/packages/mathlib/' + row['module'].replace('.', '/') + '.lean'
        raw = packages.extractfile(member).read()
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256']
        assert source_manifest['cache_provenance']['package_sources'][member] == sha(raw)
        nat_member = '.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean'
        nat_api = packages.extractfile(nat_member).read()
        assert source_manifest['cache_provenance']['package_sources'][nat_member] == sha(nat_api)
        assert b'theorem card_eq_fintype_card' in nat_api
    new = (OFFER / manifest['source']['file']).read_bytes()
    assert declarations(old) == declarations(new)
    for pattern in (r'(?m)^import .+$', r'(?m)^set_option .+$'):
        assert re.findall(pattern, old.decode()) == re.findall(pattern, new.decode())
    lexical = [inspect_bytes((OFFER / name).read_bytes(), name) for name in
               (manifest['source']['file'], manifest['checks']['file'])]
    out = HERE / 'full115-rectangular-gl-repair-capture-v2'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for original in sorted(OFFER.iterdir()):
        raw = original.read_bytes()
        (out / original.name).open('xb').write(raw)
        assert digest(out / original.name) == digest(original) == sha(raw)
        rows.append(dict(original=str(original), copy=original.name, bytes=len(raw), sha256=sha(raw)))
    result = dict(files=rows, source=SOURCE, old_sha256=sha(old), new_sha256=sha(new),
                  parent_run=marker['run'], parent_native_archive_sha256=custody['remote_sha256'],
                  exact_diff=''.join(difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True))),
                  lexical_preflight=lexical, existing_statements_imports_checks_and_options_preserved=True,
                  actual_project_and_mathlib_dependency_pins_verified=True,
                  nat_card_api=dict(member=nat_member, bytes=len(nat_api), sha256=sha(nat_api)),
                  root_read_complete_diff_map_and_manifest=True,
                  review_concern_resolved='The conversion is now inline under the actual consumer argument expected type; native verification remains required.',
                  metadata_errata='None identified in this successor.',
                  capture_control_sha256=digest(__file__), compiler_invoked=False, accepted=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(dict(folder=out.name, source_sha256=sha(new), index_sha256=digest(out / 'index.json'))), flush=True)


if __name__ == '__main__':
    main()
