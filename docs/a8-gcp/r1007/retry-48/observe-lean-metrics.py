"""Read-only metrics for exact previously observed A11 child; no compiler action."""
import runpy,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
p=Path(__file__).resolve().parent
m=runpy.run_path(str(p/'controller.py'),run_name='metrics_import'); runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T033338Z_dd58a400'
folder=run/'lean-process-metrics'; folder.mkdir(); (folder/'control').mkdir()
control=runner.Control(folder); control.authenticated=True
code,out,err=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command=ps -p 2520 -o pid,ppid,etimes,stat,pcpu,pmem,rss,vsz,args'],allow_failure=True)
c.write_new(folder/'receipt.json',c.json_bytes({'utc':c.utc(),'observed_pid':2520,'native_exit':code,'exact_run_argument_present':run.name in out.decode('utf-8','replace'),'read_only':True,'compiler_started_or_interrupted':False}))
print(out.decode('utf-8','replace'),flush=True)
