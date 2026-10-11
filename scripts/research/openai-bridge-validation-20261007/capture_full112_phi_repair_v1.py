"""Capture the offered Phi proof repair against the exact failed Full111 input."""
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


def main():
    offer = HERE / 'full112-phi-repair-v1'
    assert digest(offer / 'manifest.json') == '30C0EAE15B5DFF9064E95A73D02E3D5EE8DB54A067A3E967ED336D0B455317B3'
    manifest = json.loads((offer / 'manifest.json').read_bytes())
    for name, pin in manifest['files'].items():
        assert Path(name).name == name
        path = offer / name
        assert path.stat().st_size == pin['bytes'] and digest(path) == pin['sha256']
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    assert marker['run'] == receipt['run'] == 'cmmsa_a8_output_20261011T035621Z_498f7ba6'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == manifest['parent_native_archive_sha256']
    assert digest(ROOT / 'input-archive.tar.gz') == '3D04E683FF88B4A5CA389F07AA64583436EAC27B31FDFC9406453021021939EF'
    name = 'lean/PvNP/RealizableHardness/ExactPhiEigenrelation.lean'
    with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
        old = archive.extractfile(name).read()
        checks = archive.extractfile(name.replace('.lean', 'Checks.lean')).read()
    assert hashlib.sha256(old).hexdigest().upper() == manifest['parent_source_sha256']
    assert checks == (offer / 'ExactPhiEigenrelationChecks.lean').read_bytes()
    new = (offer / 'ExactPhiEigenrelation.lean').read_bytes()
    text = new.decode('utf-8')
    assert not new.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
    assert not re.search(r'\b(?:sorry|admit)\b|(?m:^\s*set_option linter\.)', text)
    assert headers(old) == headers(new)
    assert re.findall(r'(?m)^import .+$', old.decode()) == re.findall(r'(?m)^import .+$', text)
    assert {p.name for p in offer.iterdir()} == set(manifest['files']) | {'manifest.json'}
    out = HERE / 'full112-phi-repair-capture-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for source in sorted(offer.iterdir()):
        before = digest(source)
        copy = out / source.name
        copy.open('xb').write(source.read_bytes())
        assert digest(source) == digest(copy) == before
        rows.append(dict(original=str(source), copy=copy.name, bytes=source.stat().st_size, sha256=before))
    result = dict(schema='full112-phi-exact-repair-capture-v1', files=rows,
        source=name, old_sha256=manifest['parent_source_sha256'], new_sha256=digest(offer / 'ExactPhiEigenrelation.lean'),
        parent_run=marker['run'], parent_native_archive_sha256=custody['remote_sha256'],
        parent_input_sha256=digest(ROOT / 'input-archive.tar.gz'),
        exact_diff=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), text.splitlines(keepends=True), fromfile='Full111/ExactPhiEigenrelation.lean', tofile='Full112/ExactPhiEigenrelation.lean')),
        root_read_complete_diff_and_argument_map=True, declarations_imports_checks_preserved=True,
        capture_control_sha256=digest(__file__), compiler_invoked=False, accepted=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(dict(folder=str(out), source_sha256=result['new_sha256'], index_sha256=digest(out / 'index.json'))))


if __name__ == '__main__':
    main()
