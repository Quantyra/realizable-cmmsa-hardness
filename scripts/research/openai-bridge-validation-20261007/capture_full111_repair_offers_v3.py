"""Capture two disjoint source-only repairs against the actual failed Full110 input."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tarfile
from custody_checks import digest, verify_local_custody
from full110_builder02_controller import ROOT
from prepare_builder02_full103 import headers

HERE = Path(__file__).resolve().parent
SCOPES = {'rectangular': ('full111-rectangular-frame-repair-v1', 'RectangularFrameFiberAverage'),
          'phi': ('full111-phi-repair-v1', 'ExactPhiEigenrelation')}


def main(scope):
    assert scope == 'phi'
    folder_name, stem = SCOPES[scope]
    offer = HERE / folder_name
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check / 'terminal-custody.json').read_bytes())
    assert terminal['run'] == marker['run'] == 'cmmsa_a8_output_20261011T025221Z_7046a7c0'
    assert terminal['terminal']['native_terminal'] and not terminal['terminal']['compile_green']
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '3CFE890E3B4666A64C4E80AA7890C974D1DAF97FE82E43753BED1F0E3E14CEB0'
    with tarfile.open(custody['repository_path'], 'r:gz') as evidence:
        diagnostic = evidence.extractfile('stage-4.stdout').read()
    assert hashlib.sha256(diagnostic).hexdigest().upper() == '7B252878CFA2665B43D115F9A5E5801179EE563C2CCEAE23A42E621ACACB5830'
    old_name = 'lean/PvNP/RealizableHardness/' + stem + '.lean'
    with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
        old = archive.extractfile(old_name).read()
        checks = archive.extractfile(old_name.removesuffix('.lean') + 'Checks.lean').read()
    after = (offer / (stem + '-v4.lean')).read_bytes()
    text = after.decode('utf-8')
    assert not after.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
    assert not re.search(r'(?m)^\s*set_option linter\.', text)
    assert not re.search(r'\b(?:sorry|admit)\b', text)
    assert headers(old) == headers(after), 'Theorem/definition headers changed'
    assert re.findall(r'(?m)^import .+$', old.decode()) == re.findall(r'(?m)^import .+$', text)
    offered_checks = offer / (stem + 'Checks-v4.lean')
    if offered_checks.exists():
        assert offered_checks.read_bytes() == checks
    paths = sorted(p for p in offer.rglob('*') if p.is_file())
    assert paths and all(p.suffix in ('.lean', '.json', '.md', '.patch', '.diff') for p in paths)
    destination = HERE / ('full111-' + scope + '-repair-capture-v1')
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for path in paths:
        relative = path.relative_to(offer)
        copy = destination / relative
        copy.parent.mkdir(parents=True, exist_ok=True)
        with path.open('rb') as source, copy.open('xb') as target:
            shutil.copyfileobj(source, target)
        assert digest(copy) == digest(path)
        rows.append(dict(original=str(path), copy=relative.as_posix(), bytes=path.stat().st_size, sha256=digest(path)))
    value = dict(schema='full111-exact-failed-input-repair-capture-v1', scope=scope, files=rows,
        parent_run=marker['run'], parent_native_archive_sha256=custody['remote_sha256'],
        parent_input_sha256=digest(ROOT / 'input-archive.tar.gz'), source=old_name,
        old_sha256=hashlib.sha256(old).hexdigest().upper(), new_sha256=digest(offer / (stem + '-v4.lean')),
        exact_diff=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), text.splitlines(keepends=True),
            fromfile='Full110/' + stem + '.lean', tofile=folder_name + '/' + stem + '.lean')),
        declaration_headers_and_imports_preserved=True, existing_checks_preserved=True,
        capture_control_sha256=digest(__file__), local_Lean_invoked=False, GCP_verified=False, accepted=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps(dict(folder=str(destination), source_sha256=value['new_sha256'], index_sha256=digest(destination / 'index.json'), files=len(rows))))


if __name__ == '__main__':
    main(sys.argv[1])
