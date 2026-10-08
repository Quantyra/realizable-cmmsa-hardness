"""Bind exact178 trace to Full92 and import all additive consumer bodies."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full92 import OUTPUT, PARENT, IMPORTS, HARNESS, capsule, require_added_import_coverage
from full92_capture_gates import validate_successor


def main():
    validate_successor()
    parent = PARENT / 'consumption-preparation-v1-dag'
    readiness = json.loads((parent / 'readiness.json').read_bytes())
    assert digest(parent / 'tooling.tar.gz') == readiness['tooling_archive_sha256'] == 'AFA147F8CB013992ADBC4B467AFE94C41AF516FDB77A086C14B3B2206F9E5412'
    with tarfile.open(parent / 'tooling.tar.gz', 'r:gz') as archive:
        files = {n: archive.extractfile(n).read() for n in archive.getnames()}
    for name, row in readiness['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    old_probe = files['probe.lean']
    files['probe.lean'] = IMPORTS + old_probe
    assert files['probe.lean'][len(IMPORTS):] == old_probe
    inputs = capsule(OUTPUT / 'input-archive.tar.gz')
    inputs[HARNESS] = files['probe.lean']
    require_added_import_coverage(inputs)
    manifest = json.loads(inputs['capture-manifest.json'])
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == manifest['requested_axioms'] and len(spec['roots']) == 178
    assert len(spec['focused_roots']) == 10
    spec['status'] = 'Full92 exact178/focused-ten tooling only; native qualification required before execution'
    files['preparation-status.json'] = (json.dumps(spec, indent=2) + '\n').encode()
    destination = OUTPUT / 'consumption-preparation-v1-dag'
    destination.mkdir()
    with tarfile.open(destination / 'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        (destination / name).write_bytes(data)
    receipt = dict(readiness, schema='full92-import-complete-consumption-preparation-v1',
                   parent_tooling_archive_sha256=digest(parent / 'tooling.tar.gz'),
                   capture_manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
                   input_archive_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
                   tooling_archive_sha256=digest(destination / 'tooling.tar.gz'),
                   files={name: {'sha256': sha(data), 'bytes': len(data)} for name, data in files.items()},
                   additive_root_import_closure_verified=True, old_probe_body_exactly_preserved=True,
                   probe_executed=False, launch_clearance=False, accepted=False)
    (destination / 'readiness.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'root': str(destination), 'roots': 178, 'focused': 10,
                      'tooling_sha256': receipt['tooling_archive_sha256'], 'probe_executed': False}))


if __name__ == '__main__':
    main()
