"""Recover already-received exact archive bytes before idle-proven VM stop."""
import json,runpy,sys,base64,shutil
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
m=runpy.run_path(str(HERE/'controller.py'),run_name='recovery20_import'); runner=m['configure'](); common=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261005T204004Z_25170909'
terminal=json.loads((run/'terminal.json').read_bytes()); expected=terminal['evidence_archive_sha256']
remote_pin=(run/'control/006.stdout').read_text().splitlines(); assert remote_pin[0].split()[0].upper()==expected
size=int(remote_pin[1]); partial=Path('C:/a8gcp/25170909.tar.gz'); short=partial.with_name('25170909-recovered.tar.gz')
assert partial.stat().st_size==9*4*1024*1024
final=base64.b64decode((run/'control/016.stdout').read_bytes(),validate=True)
assert len(final)==size-partial.stat().st_size
short.write_bytes(partial.read_bytes()+final); assert common.file_sha(short)==expected
archive=run/(run.name+'-evidence.tar.gz'); shutil.copyfile(short,archive); assert common.file_sha(archive)==expected
custody={'verified_utc':common.utc(),'before_stop':True,'short_path':str(short),'repository_path':str(archive),'short_sha256':expected,'repository_sha256':expected,'remote_sha256':expected,'recovery':'Exact final base64 chunk already received in control016 despite native nonzero; all original receipts retained.'}
common.write_new(run/'custody.json',common.json_bytes(custody))
folder=run/'settlement-recovery'; folder.mkdir(); (folder/'control').mkdir(); common.write_new(folder/'custody.json',common.json_bytes(custody))
control=runner.Control(folder); control.authenticated=True; state=control.settle()
common.write_new(folder/'supplement-terminal.json',common.json_bytes({'run':run.name,'original_terminal_sha256':common.file_sha(run/'terminal.json'),'original_terminal_preserved':True,'custody':custody,'vm_terminal_receipt':state,'commands':control.records,'local_compilation':False}))
print(json.dumps({k:state[k] for k in ['name','id','status','lastStopTimestamp']},indent=2),flush=True)
