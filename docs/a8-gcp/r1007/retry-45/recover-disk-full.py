"""Preserve failed writes, recover complete received bytes, settle exact VM once."""
import json, runpy, shutil, sys
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='disk_recovery')
runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T023135Z_1fc1ec5c'
short=Path('C:/a8gcp/1fc1ec5c.tar.gz')
expected='0605CF51F0EDE1B8FAF58B04C56933EF97ABEC49B581CD6A9616F3DEE9D0125C'
assert short.stat().st_size==38972523 and c.file_sha(short)==expected
archive=run/(run.name+'-recovered-evidence.tar.gz')
assert not archive.exists()
shutil.copyfile(short,archive)
assert c.file_sha(archive)==expected
custody={'verified_utc':c.utc(),'before_stop':True,'short_path':str(short),'repository_path':str(archive),'short_sha256':expected,'repository_sha256':expected,'remote_sha256':expected,'recovery':'Complete received archive recovered after disk-full repository copy; partial original archive and zero-byte terminal preserved.'}
c.write_new(run/'custody.json',c.json_bytes(custody))
folder=run/'disk-full-recovery'; folder.mkdir(); (folder/'control').mkdir()
c.write_new(folder/'custody.json',c.json_bytes(custody))
control=runner.Control(folder); control.authenticated=True
state=control.describe()
if state['status']!='TERMINATED': state=control.settle()
c.write_new(folder/'supplement-terminal.json',c.json_bytes({'run':run.name,'original_terminal_sha256':c.file_sha(run/'terminal.json'),'original_terminal_preserved':True,'original_repository_partial_sha256':c.file_sha(run/(run.name+'-evidence.tar.gz')),'custody':custody,'vm_terminal_receipt':state,'commands':control.records,'local_compilation':False}))
print(json.dumps({'custody_sha256':expected,'vm':state},indent=2),flush=True)
