"""Rebind complete181/focused13 tooling to Full95; no trace execution."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full95 import PARENT, OUTPUT
from full95_capture_gates import validate_successor


def main():
    validate_successor()
    parent = PARENT / 'consumption-preparation-v1-dag'
    readiness = json.loads((parent / 'readiness.json').read_bytes())
    assert digest(parent / 'tooling.tar.gz') == readiness['tooling_archive_sha256'] == '8212AC2997501ADC02BA050829A6AF54430223655A3C77F72EEE207B88B15396'
    old = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    new = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    assert old['requested_axioms'] == new['requested_axioms'] and len(new['requested_axioms']) == 181
    assert set(old['project_sources']) == set(new['project_sources']) and len(new['project_sources']) == 323
    assert old['configs'] == new['configs'] and old['stages'] == new['stages']
    assert old['cache_provenance'] == new['cache_provenance']
    with tarfile.open(parent / 'tooling.tar.gz', 'r:gz') as archive:
        files = {name: archive.extractfile(name).read() for name in archive.getnames()}
    for name, row in readiness['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == new['requested_axioms'] and len(spec['focused_roots']) == 13
    spec['status'] = 'Full95 complete181/focused13 tooling only; successor native qualification required'
    files['preparation-status.json'] = (json.dumps(spec, indent=2) + '\n').encode()
    destination = OUTPUT / 'consumption-preparation-v1-dag'
    destination.mkdir()
    with tarfile.open(destination / 'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        with (destination / name).open('xb') as stream:
            stream.write(data)
    report = dict(readiness, schema='full95-complete181-focused13-preparation-v1',
                  parent_tooling_archive_sha256=digest(parent / 'tooling.tar.gz'),
                  capture_manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
                  input_archive_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
                  tooling_archive_sha256=digest(destination / 'tooling.tar.gz'),
                  files={name: {'sha256': sha(data), 'bytes': len(data)} for name, data in files.items()},
                  probe_and_postprocessor_byte_parity=True, probe_executed=False,
                  native_qualification_pending=True, launch_clearance=False, accepted=False)
    (destination / 'readiness.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'root': str(destination), 'roots': 181, 'focused': 13,
                      'tooling_sha256': report['tooling_archive_sha256'], 'probe_executed': False}))


if __name__ == '__main__':
    main()
