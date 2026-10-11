"""Preserve complete boot, failed planner/idle, and read-only confirmation originals."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full111_builder02_controller import ROOT, VM_ID
from full112_builder02_controller import ROOT as NEXT

HERE = Path(__file__).resolve().parent
RECOVERY = ROOT/'settled-cache-recovery-v1'


def main():
    wrappers = [(ROOT,'20261011T041843900971Z-90ca7960a547',48054,0),
        (ROOT,'20261011T042044556549Z-e5fdf40fc2a6',35579,0),
        (ROOT,'20261011T042854525502Z-3c1895f34b07',89908,1),
        (ROOT,'20261011T042854477598Z-df38335f2dac',43834,1),
        (NEXT,'20261011T043947418101Z-edc361a5dcf0',16259,0),
        (NEXT,'20261011T043947405342Z-10bc412fbed6',None,0)]
    paths = {Path(__file__).resolve(), RECOVERY/'boot-once.json',RECOVERY/'boot-result.json'}
    for root,name,handle,code in wrappers:
        folder = root/'research-resume-20261011'/name
        row = json.loads((folder/'command.json').read_bytes()); assert row['native_exit'] == code
        for stream in ('stdout','stderr'): assert digest(folder/stream) == row[stream+'_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
    boot = json.loads((RECOVERY/'boot-result.json').read_bytes())
    assert boot['after']['status'] == 'RUNNING' and str(boot['after']['id']) == VM_ID
    idle, = (RECOVERY/'idle-refresh-controls').iterdir()
    inspect = ROOT/'recovery-state-inspections-v1/20261011T043948363061Z'
    planner = RECOVERY/'20261011T043228243781Z'
    for folder in (Path(boot['control']), idle, planner, inspect):
        rows = json.loads((folder/'commands.json').read_bytes())
        for row in rows:
            assert 'native_exit' in row
            for stream in ('stdout','stderr'):
                path = folder/row.get(stream+'_path',str(rows.index(row))+'.'+stream)
                assert digest(path) == row[stream+'_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
    original = json.loads((planner/'commands.json').read_bytes())
    assert [r['native_exit'] for r in original] == [0,0,0,3221225477]
    assert original[-1]['argv'][5].startswith('--command=sha256sum ')
    idle_rows = json.loads((idle/'commands.json').read_bytes())
    assert [r['native_exit'] for r in idle_rows] == [0,3221225477]
    assert (idle/'control/001.stdout').read_text().splitlines() == ['1791693244','active']
    observed = json.loads((inspect/'inspection.json').read_bytes())
    assert not observed['live_processes'] and not observed['full112_launch_present']
    assert observed['timer_stdout'].strip() == 'active' and observed['idle_last_active'].strip() == '1791693244'
    assert [r['exists'] for r in observed['scopes']] == [True,False,False,False]
    assert [r['name'] for r in observed['scopes'][0]['files']] == ['full111_settled_cache_native111_v1.py']
    assert shutil.disk_usage(HERE).free-sum(p.stat().st_size for p in paths) >= 1536*1024**2
    target = HERE/'full111-recovery-transport-checkpoint-v1'; target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows=[]
    for n,p in enumerate(sorted(paths)):
        copy=target/(f'{n:03d}-'+p.name); copy.open('xb').write(p.read_bytes()); assert digest(copy)==digest(p)
        rows.append(dict(original=str(p),copy=copy.name,bytes=p.stat().st_size,sha256=digest(p)))
    (target/'index.json').open('x').write(json.dumps(dict(files=rows,
        original_handles=[dict(root=str(root),wrapper=name,handle=handle,native_exit=code) for root,name,handle,code in wrappers],
        original_planner_failed_before_plan_invocation=True,original_idle_controller_failed=True,
        later_read_only_observation=observed,observation_does_not_relabel_failed_controllers=True,
        compiler_invoked=False,cache_execution_included=False,mathematical_acceptance=False),indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_original_files=len(rows),all_bytes_verified=True)))


if __name__ == '__main__': main()
