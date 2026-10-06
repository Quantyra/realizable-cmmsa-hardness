import runpy,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='observe50_import'); runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T083408Z_44012904'; folder=run/('stage-observation-'+c.utc().replace(':','').replace('+','').replace('-','')); folder.mkdir(); (folder/'control').mkdir()
control=runner.Control(folder); control.authenticated=True
base='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run.name+'-evidence'
command='date -u; ps -eo pid,ppid,etimes,pcpu,rss,comm,args | awk \'$6 == "lean" || $6 == "lake" || $6 == "python3"\'; for i in 0 1 2 3 4 5 6 7; do if test -f '+base+'/stage-$i.native-exit; then printf "stage-%s=" "$i"; cat '+base+'/stage-$i.native-exit; fi; done; wc -c '+base+'/stage-4.stdout '+base+'/stage-4.stderr'
code,out,err=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command='+command],allow_failure=True)
c.write_new(folder/'receipt.json',c.json_bytes({'utc':c.utc(),'read_only':True,'native_exit':code,'compiler_started':False})); print(out.decode('utf-8','replace'),flush=True)
