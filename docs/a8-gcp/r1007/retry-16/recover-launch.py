"""Resume the verified retry16 capture after orphaned prelaunch; GCP only."""
import json, runpy, sys, subprocess
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
m = runpy.run_path(str(HERE / 'controller.py'), run_name='recovery_import')
common = m['common']
gates = json.loads((HERE / 'offline-gates.json').read_bytes())
m['configure'](gates['candidate_hashes'])
capture = m['PACKAGE'] / 'captures' / m['CAPTURE']
manifest = common.verify_capture(capture)
common.local_process_check()
orphan = m['PACKAGE'] / 'runs' / 'cmmsa_a8_output_20261005T182248Z_4a61500f'
assert not (orphan / 'terminal.json').exists()
assert not (orphan / 'commands.json').exists()
assert not (HERE / 'recovery-launched.json').exists()
import runner
probe = subprocess.run(['powershell.exe', '-NoProfile', '-NonInteractive', '-Command', 'ConvertTo-Json -InputObject @(Get-CimInstance Win32_Process -Filter "name=\'python.exe\'" | Select-Object ProcessId,CreationDate,CommandLine) -Compress'], capture_output=True, check=True)
common.write_new(HERE / 'recovery-processes.json', probe.stdout)
rows = json.loads(probe.stdout.decode('utf-8-sig'))
assert not any(p['ProcessId'] in [25268,50452] for p in rows)
assert not any(('controller.py launch' in (p.get('CommandLine') or '') or 'cloud_capture.py' in (p.get('CommandLine') or '')) for p in rows)
control = runner.Control(HERE / 'recovery-control')
state = control.describe()
assert state['status'] == 'TERMINATED'
common.write_new(HERE / 'orphan-prelaunch-terminal.json', common.json_bytes({'orphan_run':orphan.name,'original_bytes_preserved':{p.name:common.file_sha(p) for p in orphan.iterdir() if p.is_file()},'process_inventory_sha256':common.file_sha(HERE/'recovery-processes.json'),'original_pids_absent':[25268,50452],'fresh_vm':state,'compiler_result':'NOT STARTED','reason':'Original controller absent and VM has unchanged start/stop timestamps; no command or VM-before receipt exists. Original interruption cause unobserved.','zero_helper_credit':True}))
common.write_new(HERE/'recovery-launched.json',common.json_bytes({'capture':capture.name,'manifest_sha256':common.file_sha(capture/'manifest.json'),'recovery_script_sha256':common.file_sha(__file__),'reuse_existing_VM':True,'created_resources':[],'stop_loss':'existing idle timer and remote 70min hard stop; raw custody before idle-proven shutdown'}))
original = runner.Control.cloud
def cloud(self, args, **kwargs):
    if any(a.startswith('--command=ps -eo') for a in args):
        args = [('--command='+m['old'].old.PROBE_COMMAND) if a.startswith('--command=ps -eo') else a for a in args]
        code,out,err = original(self,args,**kwargs)
        assert code == 0 and out.strip() == b'CMMSA_RETRY14_IDLE'
        return code,b'',err
    return original(self,args,**kwargs)
runner.Control.cloud = cloud
raise SystemExit(runner.execute(capture, manifest))
