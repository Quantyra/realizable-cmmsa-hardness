"""Capture exact rectangular GL repair and its project/Mathlib dependencies."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full103 import headers
from full111_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'full112-rectangular-gl-repair-v1'
    assert digest(offer / 'OFFER-MANIFEST.json') == '81F5FA274FAA21B6DA42E06E7208C6BC9998FBDB2D0DB2A7956D6DE1FC7B3124'
    manifest = json.loads((offer / 'OFFER-MANIFEST.json').read_bytes())
    for row in manifest['files']:
        assert Path(row['path']).name == row['path']
        path = offer / row['path']
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256'].upper()
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    assert marker['run'] == receipt['run'] == 'cmmsa_a8_output_20261011T035621Z_498f7ba6'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == manifest['diagnostic_evidence']['sha256'].upper()
    assert digest(ROOT / 'input-archive.tar.gz') == manifest['source_origin']['sha256'].upper()
    name = 'lean/PvNP/RealizableHardness/RectangularGLRowCompletion.lean'
    with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
        old = archive.extractfile(name).read()
        checks = archive.extractfile(name.replace('.lean', 'Checks.lean')).read()
        for row in manifest['unchanged_project_dependencies_from_source_origin']:
            data = archive.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    assert sha(old) == manifest['source_origin']['member_sha256'].upper()
    assert checks == (offer / 'RectangularGLRowCompletionChecks.lean').read_bytes()
    packages = check / 'qualified-native' / marker['run'] / 'remote-evidence/package-sources.tar.gz'
    with tarfile.open(packages, 'r:gz') as archive:
        for row in manifest['inspected_mathlib_api_source_snapshot']['files']:
            data = archive.extractfile('.lake/packages/mathlib/Mathlib/' + row['path']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    new = (offer / 'RectangularGLRowCompletion.lean').read_bytes()
    text = new.decode('utf-8')
    assert not new.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
    assert not re.search(r'\b(?:sorry|admit)\b|(?m:^\s*set_option linter\.)', text)
    assert headers(old) == headers(new)
    assert re.findall(r'(?m)^import .+$', old.decode()) == re.findall(r'(?m)^import .+$', text)
    assert {p.name for p in offer.iterdir()} == {r['path'] for r in manifest['files']} | {'OFFER-MANIFEST.json'}
    out = HERE / 'full112-rectangular-gl-repair-capture-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for source in sorted(offer.iterdir()):
        before = digest(source)
        copy = out / source.name
        copy.open('xb').write(source.read_bytes())
        assert digest(source) == digest(copy) == before
        rows.append(dict(original=str(source), copy=copy.name, bytes=source.stat().st_size, sha256=before))
    result = dict(schema='full112-rectangular-gl-exact-repair-capture-v1', files=rows,
        source=name, old_sha256=sha(old), new_sha256=sha(new), parent_run=marker['run'],
        parent_native_archive_sha256=custody['remote_sha256'], parent_input_sha256=digest(ROOT / 'input-archive.tar.gz'),
        exact_diff=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), text.splitlines(keepends=True), fromfile='Full111/RectangularGLRowCompletion.lean', tofile='Full112/RectangularGLRowCompletion.lean')),
        root_read_complete_diff_and_argument_map=True, declarations_imports_checks_preserved=True,
        mathlib_dependency_pins_reconciled_with_actual_full111_native_archive=True,
        bounded_heartbeat_change=dict(theorem='row_prefix_uniform_mean', before=200000, after=400000, reason='Actual Full111 deterministic whnf timeout', no_warning_suppression=True),
        capture_control_sha256=digest(__file__), compiler_invoked=False, accepted=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(dict(folder=str(out), source_sha256=sha(new), index_sha256=digest(out / 'index.json'))))


if __name__ == '__main__':
    main()
