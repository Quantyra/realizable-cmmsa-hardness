"""Capture the corrected GL value declaration and exact dependencies; no compiler."""
import difflib
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full113 import OUTPUT as PARENT
from lean_source_static_preflight_v2 import inspect_bytes
from full114_gl_repair_structure_v1 import validate

HERE = Path(__file__).resolve().parent
OFFER = HERE / 'full114-rectangular-gl-repair-v2'
SOURCE = 'lean/PvNP/RealizableHardness/RectangularGLRowCompletion.lean'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    assert digest(OFFER / 'manifest.json') == '6CCA7315885DC8A4D08CCF6A93F275FE8CDAE95ACA328B335BDB35C9DEE2C1BC'
    manifest = json.loads((OFFER / 'manifest.json').read_bytes())
    assert digest(PARENT / 'input-archive.tar.gz') == manifest['input']['failed_input_archive_sha256']
    packet = HERE / manifest['input']['diagnostic_packet']
    assert digest(packet / 'index.json') == manifest['input']['diagnostic_index_sha256']
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == manifest['input']['failed_native_custody_archive_sha256']
    assert set(p.name for p in OFFER.iterdir()) == set(manifest['offered_files']) | {'manifest.json'}
    for name, row in manifest['offered_files'].items():
        assert (OFFER/name).stat().st_size == row['bytes'] and digest(OFFER/name) == row['sha256']
    with tarfile.open(PARENT/'input-archive.tar.gz', 'r:gz') as archive:
        old = archive.extractfile(SOURCE).read()
        assert sha(old) == manifest['source']['input_sha256']
        assert archive.extractfile(SOURCE.replace('.lean', 'Checks.lean')).read() == (OFFER/manifest['checks']['file']).read_bytes()
        for row in manifest['project_dependencies']:
            data = archive.extractfile(row['path']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256']
        source_manifest = json.load(archive.extractfile('capture-manifest.json'))
    packages = check/'qualified-native'/marker['run']/'remote-evidence/package-sources.tar.gz'
    assert digest(packages) == '3D4C0038AC4CFC0D8A901DC8CFD8887EC71F172EF33CF19C4B0D9D1AFBAED638'
    with tarfile.open(packages, 'r:gz') as archive:
        for row in manifest['external_dependencies']:
            member = '.lake/packages/mathlib/' + row['module'].replace('.', '/') + '.lean'
            data = archive.extractfile(member).read()
            assert len(data) == row['source_bytes'] and sha(data) == row['source_sha256']
            assert source_manifest['cache_provenance']['package_sources'][member] == sha(data)
    new = (OFFER/manifest['source']['file']).read_bytes()
    assert sha(new) == manifest['source']['candidate_sha256']
    lexical = [inspect_bytes((OFFER/name).read_bytes(), name) for name in
               (manifest['source']['file'], manifest['checks']['file'])]
    structure = validate(old, new)
    out = HERE/'full114-rectangular-gl-repair-capture-v1'
    out.mkdir(exist_ok=False)
    (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for original in sorted(OFFER.iterdir()):
        raw = original.read_bytes()
        (out/original.name).open('xb').write(raw)
        assert digest(out/original.name) == digest(original) == sha(raw)
        rows.append(dict(original=str(original), copy=original.name, bytes=len(raw), sha256=sha(raw)))
    diff = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), new.decode().splitlines(keepends=True), fromfile='Full113', tofile='Full114'))
    result = dict(files=rows, source=SOURCE, old_sha256=sha(old), new_sha256=sha(new),
        parent_run=marker['run'], parent_native_archive_sha256=custody['remote_sha256'],
        exact_diff=diff, lexical_preflight=lexical, structure=structure,
        existing_statements_imports_and_checks_preserved=True,
        actual_full113_project_and_mathlib_dependency_pins_verified=True,
        root_read_complete_diff_and_map_and_manifest=True,
        bounded_heartbeat_change=dict(before=800000, after=400000, theorem='row_prefix_uniform_mean'),
        offer_metadata_errata=[
            'Historical diagnostics field in offered manifest still says haveI; exact raw warning recommends ordinary let over letI, and repaired source uses let.',
            'Offered map contains a lone carriage return before owPrefix_fiber_equiv; read as rowPrefix_fiber_equiv. No Lean source is affected.'
        ],
        capture_control_sha256=digest(__file__), structure_control_sha256=digest(HERE/'full114_gl_repair_structure_v1.py'),
        compiler_invoked=False, accepted=False)
    (out/'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps(dict(folder=out.name, source_sha256=sha(new), index_sha256=digest(out/'index.json'))), flush=True)


if __name__ == '__main__':
    main()
