"""Recover exact received archive bytes, then idle-proven same-VM settlement."""
import json,runpy,sys,shutil
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
m=runpy.run_path(str(HERE/'controller.py'),run_name='recovery_import')
runner=m['configure']()
common=m['common']; run=m['PACKAGE']/'runs/cmmsa_a8_output_20261005T200559Z_dec38ed7'
archive=run/(run.name+'-evidence.tar.gz'); short=Path('C:/a8gcp/dec38ed7-recovered.tar.gz')
expected='6E98C2A11D00BA53925584EE31F691F0CBA17AF424877ECABB91E2B043AEFC77'
assert common.file_sha(archive)==common.file_sha(short)==expected
custody={'verified_utc':common.utc(),'before_stop':True,'short_path':str(short),'repository_path':str(archive),'short_sha256':expected,'repository_sha256':expected,'remote_sha256':expected,'recovery':'Exact final base64 chunk already received in control016 despite native nonzero; original partial/archive/control receipts preserved.'}
common.write_new(run/'custody.json',common.json_bytes(custody))
folder=run/'settlement-recovery'; folder.mkdir(); (folder/'control').mkdir()
common.write_new(folder/'custody.json',common.json_bytes(custody))
control=runner.Control(folder); control.authenticated=True
state=control.settle()
common.write_new(folder/'supplement-terminal.json',common.json_bytes({'run':run.name,'original_terminal_sha256':common.file_sha(run/'terminal.json'),'original_terminal_preserved':True,'custody':custody,'vm_terminal_receipt':state,'commands':control.records,'local_compilation':False}))
print(json.dumps(state,indent=2),flush=True)
