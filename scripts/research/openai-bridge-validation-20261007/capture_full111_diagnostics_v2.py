"""Retain complete native streams and exact source bodies for disjoint repairs."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from full111_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    assert marker['run'] == receipt['run'] == 'cmmsa_a8_output_20261011T035621Z_498f7ba6'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '29A942FBF1594E1C09EC34ECE58DB02F1742E8B9FDCDA0E88B3084E3F4B7F192'
    assert digest(ROOT / 'input-archive.tar.gz') == '3D04E683FF88B4A5CA389F07AA64583436EAC27B31FDFC9406453021021939EF'
    out = HERE / 'full111-native-diagnostic-packet-v2'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []

    def retain(name, data, origin):
        (out / name).open('xb').write(data)
        assert (out / name).read_bytes() == data
        rows.append(dict(copy=name, original=origin, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))

    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        for name in ('stage-4.stdout', 'stage-4.stderr', 'dedicated-worker-terminal.json'):
            retain(name, archive.extractfile(name).read(), custody['repository_path'] + '!' + name)
    with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
        for stem in ('ExactPhiEigenrelation', 'RectangularGLRowCompletion'):
            for suffix in ('.lean', 'Checks.lean'):
                name = 'lean/PvNP/RealizableHardness/' + stem + suffix
                data = archive.extractfile(name).read()
                assert manifest['project_sources'][name] == dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper())
                retain(stem + suffix, data, str(ROOT / 'input-archive.tar.gz') + '!' + name)
    raw = (out / 'stage-4.stdout').read_bytes()
    text = raw.decode('utf-8')
    parts = re.split(r'(?m)(?=^(?:error: |warning: |[✔⚠✖] |Some required targets))', text)
    selected = ''.join(p for p in parts if re.match(r'^(?:error|warning): lean/PvNP/RealizableHardness/(?:ExactPhiEigenrelation|RectangularGLRowCompletion)\.lean:', p))
    retain('selected-diagnostics.txt', selected.encode('utf-8'), 'Complete selected diagnostic blocks derived from exact stage-4.stdout')
    retain('terminal-custody.json', (check / 'terminal-custody.json').read_bytes(), str(check / 'terminal-custody.json'))
    assert len(re.findall(r'(?m)^error:', text)) == 9
    result = dict(schema='full111-exact-native-diagnostic-packet-v1', files=rows, run=marker['run'],
                  complete_stage4_streams=True, original_native_exit=1,
                  stages=[0, 0, 0, 0, 1, 125, 125], errors=9, unsolved_goals=2,
                  selected_blocks_are_derived_not_raw=True, acceptance=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(folder=str(out), complete_files=len(rows), errors=9)))


if __name__ == '__main__':
    main()
