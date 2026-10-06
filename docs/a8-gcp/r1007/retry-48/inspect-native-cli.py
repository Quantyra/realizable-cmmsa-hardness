"""Read pinned compiler CLI help only; never compile a second target."""
import runpy,sys,json
from pathlib import Path
sys.dont_write_bytecode=True
p=Path(__file__).resolve().parent
m=runpy.run_path(str(p/'controller.py'),run_name='cli_inspection'); runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T033338Z_dd58a400'
folder=run/'native-cli-help'; folder.mkdir(); (folder/'control').mkdir()
control=runner.Control(folder); control.authenticated=True
code,out,err=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command=/home/dfredriksen_quantyra_org/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean --help'],allow_failure=True)
c.write_new(folder/'receipt.json',c.json_bytes({'utc':c.utc(),'native_exit':code,'help_only':True,'formal_compilation':False,'profiling_flag_documented':b'--profile' in out}))
print('\n'.join(line for line in out.decode('utf-8','replace').splitlines() if 'profile' in line or 'timeout' in line),flush=True)
