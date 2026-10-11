"""Preserve all eight complete plans and each original controller outcome."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
from custody_checks import digest
from run_full111_settled_cache_openssh_v5 import RECOVERY, NUMBERS
from audit_full111_settled_cache_recovery_v4 import unique_operation
from full112_builder02_controller import ROOT as NEXT

HERE = Path(__file__).resolve().parent
WRAPPERS = [
    (69502, 1, '20261011T044607572150Z-1fdee324a245', [111,96,97,98]),
    (53176, 0, '20261011T045435334132Z-5e727800d586', [109,110,'111_small']),
    (36481, 0, '20261011T050035213455Z-bdbff64d465d', ['111_tail']),
]

def main():
    assert not (RECOVERY/'execution-request-once-v2.json').exists()
    scopes = json.loads((HERE/'full111-settled-cache-recovery-derivation-v4.json').read_bytes())['scopes']
    assert [s['number'] for s in scopes] == NUMBERS
    paths = {Path(__file__).resolve(), HERE/'full111-settled-cache-recovery-derivation-v4.json'}
    summaries, plans, folders = [], {}, {}
    for scope in scopes:
        p, record = unique_operation(scope['number'], 'plan')
        folder = p.parent
        folders[scope['number']] = folder
        assert record['remote_control'] == scope['remote_control']
        assert record['helper_sha256'] == scope['helper_sha256'] == digest(HERE/scope['helper']) == digest(folder/scope['helper'])
        value = json.loads(Path(record['local_result']).read_bytes())
        assert not value['executed'] and not value['compiler_invoked']
        assert value['original_archive_sha256'] == scope['archive_sha256']
        assert value['old_root'] == '/home/dfredriksen_quantyra_org/'+scope['run']+'/.lake/packages'
        assert value['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
        rows = value['rows']
        assert rows and len({r['relative'] for r in rows}) == len(rows)
        for row in rows:
            rel = PurePosixPath(row['relative'])
            assert not rel.is_absolute() and '..' not in rel.parts
            assert {'.lake','build','lib','lean'} <= set(rel.parts)
            assert rel.name.endswith(('.olean','.olean.private','.olean.server','.ilean'))
            assert row['bytes'] > 0 and row['allocated_bytes'] > 0
            assert len(row['sha256']) == 64 and all(c in '0123456789ABCDEF' for c in row['sha256'])
        assert sum(r['allocated_bytes'] for r in rows) == value['allocated_bytes'] >= scope['target_bytes']
        plans[scope['number']] = value
        summaries.append(dict(number=scope['number'],rows=len(rows),allocated_bytes=value['allocated_bytes'],
            plan_sha256=record['result_sha256'],helper_sha256=record['helper_sha256']))
        paths.add(HERE/scope['helper'])
    used = set()
    for scope in scopes:
        for row in plans[scope['number']]['rows']:
            key = (scope['run'], row['relative'])
            assert key not in used, key
            used.add(key)
    assert all(r['bytes'] >= 65536 for n in (111,'111_tail') for r in plans[n]['rows'])
    assert all(r['bytes'] < 65536 for r in plans['111_small']['rows'])
    originals = []
    for handle, expected_exit, stamp, numbers in WRAPPERS:
        folder = folders[numbers[0]]
        assert all(folders[n] == folder for n in numbers)
        wrapper = NEXT/'research-resume-20261011'/stamp
        command = json.loads((wrapper/'command.json').read_bytes())
        assert command['native_exit'] == expected_exit
        for stream in ('stdout','stderr'):
            assert digest(wrapper/stream) == command[stream+'_sha256']
        assert digest(wrapper/Path(command['argv'][7]).name) == command['source_sha256']
        commands = json.loads((folder/'transport/commands.json').read_bytes())
        failures = [i for i,r in enumerate(commands) if r['native_exit'] != 0]
        assert failures == ([14] if handle == 69502 else [])
        assert commands[-1]['argv'][0] == 'taskkill.exe' and commands[-1]['native_exit'] == 0
        for i,row in enumerate(commands):
            for stream in ('stdout','stderr'):
                assert digest(Path(row[stream+'_path'])) == row[stream+'_sha256']
            if 'stdin_sha256' in row:
                assert digest(folder/'transport'/f'{i:03d}.stdin') == row['stdin_sha256']
        if expected_exit:
            assert commands[14]['native_exit'] == 1 and not (folder/'result.json').exists()
            assert 'Insufficient identical dependency-object copies; no changes made' in (folder/'transport/014.stderr').read_text()
        else:
            result = json.loads((folder/'result.json').read_bytes())
            assert result['original_operations_settled'] and not result['compiler_invoked']
            assert [r['number'] for r in result['operations']] == numbers
        paths.update(p for root in (folder,wrapper) for p in root.rglob('*') if p.is_file())
        originals.append(dict(handle=handle,native_exit=expected_exit,wrapper=str(wrapper),folder=str(folder),complete_plan_scopes=numbers))
    assert shutil.disk_usage(HERE).free >= 1536*1024**2 + 16*1024**2
    target = HERE/'full111-recovery-plans-openssh-record-v5'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive = target/'complete-originals.tar.gz'
    rows = []
    with tarfile.open(archive,'x:gz',compresslevel=9) as tar:
        for i,p in enumerate(sorted(paths)):
            member = f'{i:03d}-'+p.name
            row = dict(original=str(p),member=member,bytes=p.stat().st_size,sha256=digest(p))
            tar.add(p,arcname=member,recursive=False)
            assert digest(p) == row['sha256']
            rows.append(row)
    with tarfile.open(archive,'r:gz') as tar:
        assert len(tar.getmembers()) == len(rows)
        for row in rows:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
            assert digest(Path(row['original'])) == row['sha256']
    assert shutil.disk_usage(HERE).free >= 1536*1024**2
    index = dict(files=[dict(copy=archive.name,bytes=archive.stat().st_size,sha256=digest(archive))],
        originals=rows,controllers=originals,scopes=summaries,all_eight_plans_verified=True,
        all_candidate_paths_pairwise_disjoint_within_each_run=True,execution_included=False,
        every_original_archive_member_roundtrip_verified=True,compiler_invoked=False,mathematical_acceptance=False)
    (target/'index.json').open('x').write(json.dumps(index,indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_originals=len(rows),archive_sha256=digest(archive),scopes=summaries)),flush=True)

if __name__ == '__main__':
    main()

