"""Preserve complete terminal recovery phases as an exact roundtripping archive."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
from custody_checks import digest
from full118_builder02_controller import ROOT
from run_full118_cache_recovery_v2 import RECOVERY, DERIVATION, verified_plans as additive_plans
from audit_full118_cache_recovery_v3 import verified_plans as cumulative_plans

HERE = Path(__file__).resolve().parent


def main(phase):
    assert phase == 'complete'
    inspection=json.loads((HERE/'full118-owned-capacity-inspection-record-v1/index.json').read_bytes())
    assert inspection['native_exit']==0 and inspection['original_handle']==23226
    summaries = additive_plans() if phase=='plans' else cumulative_plans()
    if phase == 'complete':
        from audit_full118_cache_recovery_v3 import validate_local_audit, AUDIT
        report = validate_local_audit()
    paths = {Path(__file__).resolve(), DERIVATION}
    wrappers = []
    for folder in (ROOT / 'research-resume-20261011').iterdir():
        command = folder / 'command.json'
        if not command.is_file():
            continue
        record = json.loads(command.read_bytes())
        name = Path(record['argv'][7]).name if len(record['argv']) > 7 else ''
        allowed = {'run_full118_cache_recovery_v1.py','audit_full118_cache_recovery_v1.py','run_full118_cache_recovery_v2.py','run_full118_cache_recovery_v3.py','audit_full118_cache_recovery_v2.py','audit_full118_cache_recovery_v3.py'}
        if name not in allowed:
            continue
        assert record['native_exit']==0 or (name=='audit_full118_cache_recovery_v1.py' and record['native_exit']==1 and folder.name=='20261012T013347352693Z-26c9d2206a10'),(folder,record)
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == record[stream + '_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
        wrappers.append(dict(folder=str(folder), action=record['argv'][7:], native_exit=record['native_exit'],historical_failed_capacity_gate_preserved=record['native_exit']==1))
    for folder in (RECOVERY, ROOT / 'staging-controls', ROOT / 'capacity-inspections-v2', ROOT / 'generated-capacity-inspections-v1', ROOT / 'generated-capacity-inspections-v2', ROOT / 'generated-capacity-inspections-v3'):
        if folder.is_dir():
            paths.update(p for p in folder.rglob('*') if p.is_file())
    assert len(wrappers) >= (1 if phase=='plans' else 3)
    if phase == 'plans':
        assert not (RECOVERY / 'execution-request-once-additive-v2.json').exists()
    target = HERE / ('full118-recovery-' + ('additive-plans-record-v3' if phase == 'plans' else 'complete-record-v5'))
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    parent_paths=[HERE/'full118-recovery-plans-record-v1/index.json',HERE/'full118-failed-recovery-capacity-audit-record-v1/index.json']
    if phase=='complete':parent_paths.append(HERE/'full118-recovery-additive-plans-record-v3/index.json')
    covered={};parent_pins=[];archive_cache={};index_cache={};cache_bytes=0
    def retained_bytes(index_path,row,depth=0):
        assert depth<8
        if 'custody_parent' in row:
            ref=row['custody_parent'];p=Path(ref['index']);assert digest(p)==ref['sha256']
            j=json.loads(p.read_bytes());matches=[r for r in j['files'] if r['original']==row['original'] and r['sha256']==row['sha256']];assert len(matches)==1
            return retained_bytes(p,matches[0],depth+1)
        nonlocal cache_bytes
        key=str(index_path)
        if key not in index_cache:index_cache[key]=json.loads(index_path.read_bytes())
        j=index_cache[key];payload=index_path.parent/j['payload']['file']
        if key not in archive_cache:
            assert digest(payload)==j['payload']['sha256'];members={}
            with tarfile.open(payload,'r|gz') as t:
                for member in t:
                    assert member.isfile() and member.name not in members
                    b=t.extractfile(member).read();cache_bytes+=len(b);assert cache_bytes<=192*1024**2,'Bounded parent byte cache required';members[member.name]=b
            archive_cache[key]=members
        return archive_cache[key][row['member']]
    for p in parent_paths:
        j=json.loads(p.read_bytes());parent_pins.append(dict(index=str(p),sha256=digest(p)))
        for r in j['files']:covered[(r['original'],r['sha256'])]=(p,r)
    rows=[];archive=target/'complete-new-originals.tar.gz'
    with archive.open('xb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as compressed:
            with tarfile.open(fileobj=compressed,mode='w') as tar:
                for i,path in enumerate(sorted(paths)):
                    data=path.read_bytes();pin=hashlib.sha256(data).hexdigest().upper();key=(str(path),pin)
                    row=dict(original=str(path),bytes=len(data),sha256=pin)
                    if key in covered:
                        parent,old=covered[key];assert retained_bytes(parent,old)==data
                        row['custody_parent']=dict(index=str(parent),sha256=digest(parent))
                    else:
                        member=f'{i:03d}-'+path.name;info=tarfile.TarInfo(member);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data));row['member']=member
                    assert digest(path)==pin;rows.append(row)
    with tarfile.open(archive,'r:gz') as tar:
        for row in rows:
            if 'custody_parent' in row:
                p=Path(row['custody_parent']['index']);old=[r for r in json.loads(p.read_bytes())['files'] if r['original']==row['original'] and r['sha256']==row['sha256']];assert len(old)==1;data=retained_bytes(p,old[0])
            else:data=tar.extractfile(row['member']).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256'] and digest(Path(row['original']))==row['sha256']
    value = dict(schema='full118-cumulative-exact-recovery-phase-custody-v3', phase=phase, files=rows, wrappers=wrappers,
        direct_all_scope_inspection_handle=23226, direct_all_scope_inspection_exit=0,
        scopes=summaries, all_selected_plans_verified=True, execution_included=phase == 'complete', prior_execution_and_failed_capacity_audit_preserved=True,
        hash_pinned_parent_archives=parent_pins, prior_evidence_bytes_omitted=False, payload=dict(file=archive.name, bytes=archive.stat().st_size, sha256=digest(archive)),
        all_members_roundtrip_verified=True, files_deleted=False, compiler_invoked=False, mathematical_acceptance=False)
    if phase == 'complete':
        value.update(independent_audit=dict(path=str(AUDIT / 'audit.json'), sha256=digest(AUDIT / 'audit.json')),
            plans_custody_sha256=digest(HERE / 'full118-recovery-additive-plans-record-v3/index.json'))
    (target / 'index.json').open('x').write(json.dumps(value, indent=2) + '\n')
    print(json.dumps(dict(folder=str(target), originals=len(rows), payload_bytes=archive.stat().st_size, payload_sha256=digest(archive))), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
