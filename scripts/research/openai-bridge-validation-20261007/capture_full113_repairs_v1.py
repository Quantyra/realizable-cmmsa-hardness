"""Capture exact Full113 repair offers after root source and argument review."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full103 import headers
from full112_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
OFFERS = [
    ('rectangular-gl', 'manifest.json', '0A591957E840DC8CAAE9D758EAEA25B7F6F19468C2C64E9094B4ADB269369E47', 'RectangularGLRowCompletion.lean'),
    ('complex-append', 'OFFER-MANIFEST.json', 'C8A9B41B36BD8198332C22E18D2D71FF8B890A5D1CD08EBEB3BE73E5A2A78829', 'ExactComplexAppendContinuation.lean'),
]


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    assert marker['run'] == receipt['run'] == 'cmmsa_a8_output_20261011T051406Z_3ef6ddc2'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '0392E798A4234ADC4386703FDB1817217D99DFBEA7FF48D4184E614AA42FD6B2'
    assert digest(ROOT / 'input-archive.tar.gz') == '1686A96C43231E3E02D88468C6EE5B176D131FF96B2A1F44C3C85C3E5CE531AA'
    packet = HERE / 'full112-native-diagnostic-packet-v1'
    assert digest(packet / 'index.json') == 'A0CC0804ED5ABA8F393BEAFC5F65EFE2251324CDCBE24AC80462B7CBAAE9D249'
    packet_hashes = {digest(p) for p in packet.iterdir() if p.is_file()}
    packages = check / 'qualified-native' / marker['run'] / 'remote-evidence/package-sources.tar.gz'
    assert digest(packages) == '2DFA036C84860818068E8F5B64C203AE9F86A51DDB966B745B0743A988E50414'
    for lane, manifest_name, pin, filename in OFFERS:
        offer = HERE / ('full113-' + lane + '-repair-v1')
        assert digest(offer / manifest_name) == pin
        manifest = json.loads((offer / manifest_name).read_bytes())
        if lane == 'rectangular-gl':
            files = [dict(path=name, **row) for name, row in manifest['files'].items()]
            dependencies = manifest['project_imports_from_full112_archive']
            ext = manifest['mathlib_import']
            external = [dict(member=ext['source_member'], bytes=ext['source_bytes'], sha256=ext['source_sha256'])]
            old_sha = manifest['input_capture']['source_sha256']
            diagnostics_sha = manifest['input_capture']['diagnostics_sha256']
        else:
            files = manifest['files']
            dependencies = [dict(member=row['path'], bytes=row['bytes'], sha256=row['sha256']) for row in manifest['pinned_full112_inputs']['project_members']]
            external = [manifest['pinned_mathlib'][name] for name in ('Complex.Basic', 'Complex.BigOperators')]
            old_sha = manifest['parent_diagnostic_packet']['original_source_sha256']
            diagnostics_sha = manifest['parent_diagnostic_packet']['diagnostics_sha256']
        assert diagnostics_sha in packet_hashes
        assert {p.name for p in offer.iterdir()} == {r['path'] for r in files} | {manifest_name}
        for row in files:
            assert Path(row['path']).name == row['path']
            p = offer / row['path']
            assert p.stat().st_size == row['bytes'] and digest(p) == row['sha256'].upper()
        source = 'lean/PvNP/RealizableHardness/' + filename
        checks_name = filename.replace('.lean', 'Checks.lean')
        with tarfile.open(ROOT / 'input-archive.tar.gz', 'r:gz') as archive:
            old = archive.extractfile(source).read()
            assert sha(old) == old_sha
            assert archive.extractfile(source.replace('.lean', 'Checks.lean')).read() == (offer / checks_name).read_bytes()
            for row in dependencies:
                data = archive.extractfile(row['member']).read()
                assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        with tarfile.open(packages, 'r:gz') as archive:
            for row in external:
                data = archive.extractfile(row['member']).read()
                assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        new = (offer / filename).read_bytes()
        text = new.decode('utf-8')
        for name in (filename, checks_name):
            raw = (offer / name).read_bytes()
            value = raw.decode('utf-8')
            assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in value
            assert not re.search(r'\b(?:sorry|admit)\b|(?m:^\s*set_option linter\.)', value)
        assert headers(old) == headers(new)
        assert re.findall(r'(?m)^import .+$', old.decode()) == re.findall(r'(?m)^import .+$', text)
        out = HERE / ('full113-' + lane + '-repair-capture-v1')
        out.mkdir(exist_ok=False)
        (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
        rows = []
        for original in sorted(offer.iterdir()):
            before = digest(original)
            target = out / original.name
            target.open('xb').write(original.read_bytes())
            assert digest(original) == digest(target) == before
            rows.append(dict(original=str(original), copy=target.name, bytes=target.stat().st_size, sha256=before))
        diff = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), text.splitlines(keepends=True), fromfile='Full112/' + filename, tofile='Full113/' + filename))
        result = dict(schema='full113-exact-two-body-repair-capture-v1', files=rows, source=source,
            old_sha256=sha(old), new_sha256=sha(new), parent_run=marker['run'],
            parent_native_archive_sha256=custody['remote_sha256'], parent_input_sha256=digest(ROOT / 'input-archive.tar.gz'),
            exact_diff=diff, root_read_complete_source_diff_and_argument_map=True,
            declarations_imports_checks_preserved=True, project_and_mathlib_dependency_pins_verified=True,
            bounded_heartbeat_change=(dict(theorem='row_prefix_uniform_mean', before=400000, after=800000, reason='Full112 deterministic whnf timeout') if lane == 'rectangular-gl' else None),
            capture_control_sha256=digest(__file__), compiler_invoked=False, accepted=False)
        (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
        print(json.dumps(dict(folder=out.name, source_sha256=sha(new), index_sha256=digest(out / 'index.json'))), flush=True)
        print(diff, flush=True)


if __name__ == '__main__':
    main()
