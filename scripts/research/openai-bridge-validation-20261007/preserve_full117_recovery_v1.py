"""Preserve complete terminal recovery phases as an exact roundtripping archive."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
from custody_checks import digest
from full117_builder02_controller import ROOT
from run_full117_cache_recovery_v1 import RECOVERY, DERIVATION, verified_plans

HERE = Path(__file__).resolve().parent


def main(phase):
    assert phase in ('plans', 'complete')
    inspection=json.loads((HERE/'full117-owned-capacity-inspection-record-v1/index.json').read_bytes())
    assert inspection['native_exit']==0 and inspection['original_handle']==53918
    summaries = verified_plans()
    if phase == 'complete':
        from audit_full117_cache_recovery_v1 import validate_local_audit, AUDIT
        report = validate_local_audit()
    paths = {Path(__file__).resolve(), DERIVATION}
    wrappers = []
    for folder in (ROOT / 'research-resume-20261011').iterdir():
        command = folder / 'command.json'
        if not command.is_file():
            continue
        record = json.loads(command.read_bytes())
        name = Path(record['argv'][7]).name if len(record['argv']) > 7 else ''
        allowed = {'run_full117_cache_recovery_v1.py','audit_full117_cache_recovery_v1.py'}
        if name not in allowed:
            continue
        assert record['native_exit'] == 0, (folder, record)
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == record[stream + '_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
        wrappers.append(dict(folder=str(folder), action=record['argv'][7:], native_exit=record['native_exit']))
    for folder in (RECOVERY, ROOT / 'staging-controls', ROOT / 'capacity-inspections-v2', ROOT / 'generated-capacity-inspections-v1', ROOT / 'generated-capacity-inspections-v2', ROOT / 'generated-capacity-inspections-v3'):
        if folder.is_dir():
            paths.update(p for p in folder.rglob('*') if p.is_file())
    assert len(wrappers) >= (1 if phase=='plans' else 3)
    if phase == 'plans':
        assert not (RECOVERY / 'execution-request-once.json').exists()
    target = HERE / ('full117-recovery-' + ('plans-record-v1' if phase == 'plans' else 'complete-record-v1'))
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []; archive = target / 'complete-originals.tar.gz'
    with archive.open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as tar:
                for i, path in enumerate(sorted(paths)):
                    data = path.read_bytes(); pin = hashlib.sha256(data).hexdigest().upper()
                    member = f'{i:03d}-' + path.name
                    info = tarfile.TarInfo(member); info.size = len(data); info.mode = 0o644
                    tar.addfile(info, io.BytesIO(data))
                    assert digest(path) == pin
                    rows.append(dict(original=str(path), member=member, bytes=len(data), sha256=pin))
    with tarfile.open(archive, 'r:gz') as tar:
        assert len(tar.getmembers()) == len(rows)
        for row in rows:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
            assert digest(Path(row['original'])) == row['sha256']
    value = dict(schema='full117-complete-recovery-phase-custody-v2', phase=phase, files=rows, wrappers=wrappers,
        direct_all_scope_inspection_handle=53918, direct_all_scope_inspection_exit=0,
        scopes=summaries, all_selected_plans_verified=True, execution_included=phase == 'complete',
        payload=dict(file=archive.name, bytes=archive.stat().st_size, sha256=digest(archive)),
        all_members_roundtrip_verified=True, files_deleted=False, compiler_invoked=False, mathematical_acceptance=False)
    if phase == 'complete':
        value.update(independent_audit=dict(path=str(AUDIT / 'audit.json'), sha256=digest(AUDIT / 'audit.json')),
            plans_custody_sha256=digest(HERE / 'full117-recovery-plans-record-v1/index.json'))
    (target / 'index.json').open('x').write(json.dumps(value, indent=2) + '\n')
    print(json.dumps(dict(folder=str(target), originals=len(rows), payload_bytes=archive.stat().st_size, payload_sha256=digest(archive))), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
