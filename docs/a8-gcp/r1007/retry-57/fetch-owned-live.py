"""Read-only exact provisional A12/A19 source stdout/stderr; final archive authoritative."""
from pathlib import Path
import runpy,json,sys,re
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='fetch57_import');runner=m['configure']();c=m['common']
run=m['PACKAGE']/'runs'/sys.argv[1]
folder=run/('live-owned-'+c.utc().replace(':','').replace('+','').replace('-',''));folder.mkdir();(folder/'control').mkdir()
control=runner.Control(folder);control.authenticated=True
base='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run.name+'-evidence/stage-4'
rows=[]
for stream in ['stdout','stderr']:
    code,out,err=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command=cat '+base+'.'+stream],allow_failure=True,timeout=120)
    c.write_new(folder/('native-'+stream+'.snapshot'),out)
    rows.append({'stream':stream,'native_exit':code,'bytes':len(out),'sha256':c.sha(out)})
receipt={'utc':c.utc(),'streams':rows,'provisional':True,'final_archive_authoritative':True,'compiler_started':False}
c.write_new(folder/'receipt.json',c.json_bytes(receipt))
text='\n'.join((folder/('native-'+s+'.snapshot')).read_text(encoding='utf8',errors='replace') for s in ['stdout','stderr'])
headers=[line for line in text.splitlines() if re.search(r'A12InfluenceBound\.lean:\d+:\d+:',line) and ('error:' in line or 'warning:' in line)]
print(json.dumps({'folder':str(folder),'streams':rows,'owned_header_count':len(headers),'owned_headers':headers},indent=2))
