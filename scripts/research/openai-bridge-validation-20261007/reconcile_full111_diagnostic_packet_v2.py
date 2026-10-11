"""Reconcile exact retained bytes and distinguish source headers from the legacy counter."""
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from full111_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def main():
    packet = HERE / 'full111-native-diagnostic-packet-v2'
    receipt = json.loads((packet / 'terminal-custody.json').read_bytes())
    rows = []
    with tarfile.open(receipt['custody']['repository_path'], 'r:gz') as archive:
        for name in ('stage-4.stdout', 'stage-4.stderr', 'dedicated-worker-terminal.json'):
            assert (packet / name).read_bytes() == archive.extractfile(name).read()
    with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
        for stem in ('ExactPhiEigenrelation', 'RectangularGLRowCompletion'):
            for suffix in ('.lean', 'Checks.lean'):
                name = stem + suffix
                assert (packet / name).read_bytes() == archive.extractfile('lean/PvNP/RealizableHardness/' + name).read()
    text = (packet / 'stage-4.stdout').read_text(encoding='utf-8')
    headers = re.findall(r'(?m)^error: lean/.*\.lean:\d+:\d+:.*$', text)
    assert len(headers) == 8
    assert sum('ExactPhiEigenrelation.lean:' in line for line in headers) == 3
    assert sum('RectangularGLRowCompletion.lean:' in line for line in headers) == 5
    assert receipt['terminal']['stages'][4]['diagnostics']['errors'] == 9
    parts = re.split(r'(?m)(?=^(?:error: |warning: |[✔⚠✖] |Some required targets))', text)
    selected = ''.join(p for p in parts if re.match(r'^(?:error|warning): lean/PvNP/RealizableHardness/(?:ExactPhiEigenrelation|RectangularGLRowCompletion)\.lean:', p))
    assert selected.encode('utf-8') == (packet / 'selected-diagnostics.txt').read_bytes()
    for path in sorted(packet.iterdir()):
        assert path.is_file()
        rows.append(dict(copy=path.name, bytes=path.stat().st_size, sha256=digest(path)))
    check = Path(json.loads((ROOT / 'launch-once.json').read_bytes())['preflight'])
    assert (packet / 'terminal-custody.json').read_bytes() == (check / 'terminal-custody.json').read_bytes()
    failed = HERE / 'full111-native-diagnostic-packet-v1'
    assert (failed / 'stage-4.stdout').read_bytes() == (packet / 'stage-4.stdout').read_bytes()
    assert (failed / 'stage-4.stderr').read_bytes() == (packet / 'stage-4.stderr').read_bytes()
    result = dict(schema='full111-native-diagnostic-packet-v2-reconciliation', files=rows,
        exact_source_error_headers=headers, source_error_count=8, original_terminal_broad_error_count=9,
        original_capture_v2_exit=1, original_failure='AssertionError: broad error count was incorrectly asserted against source headers',
        original_failed_control_unmodified=True, exact_packet_bytes_reverified=True,
        complete_stage4_streams=True, selected_blocks_are_derived=True,
        first_failed_partial_packet_preserved=True, native_compiler_exit=1, native_acceptance=False,
        raw_direct_tool_traceback_archived=False, root_observation_of_tool_traceback=True)
    (packet / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(packet=str(packet), exact_source_error_headers=len(headers), legacy_count=9, complete_files=len(rows))))


if __name__ == '__main__':
    main()
