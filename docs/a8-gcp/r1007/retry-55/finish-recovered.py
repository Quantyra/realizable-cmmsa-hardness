import runpy,json,tarfile,sys
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='finish55_recovery'); m['configure'](); run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T081337Z_6df39b3b'
supp=json.loads((run/'terminal-recovery.json').read_bytes()); assert supp['vm_terminal_receipt']['status']=='TERMINATED'
with tarfile.open(run/(run.name+'-evidence.tar.gz'),'r:gz') as tar:
 members=tar.getmembers(); assert all(not Path(x.name).is_absolute() and '..' not in Path(x.name).parts and not x.issym() and not x.islnk() for x in members)
 target=run/'remote-evidence'; target.mkdir(exist_ok=False); tar.extractall(target,filter='data')
text=(here/'finish-native.py').read_text(encoding='utf-8').replace("run/'terminal.json'","run/'terminal-recovery.json'")
needle="text=(m['PACKAGE']/'retry-15/finish.snapshot.py').read_text(encoding='utf-8')"
assert needle in text; text=text.replace(needle,needle+"\ntext=text.replace(\"run/'terminal.json'\",\"run/'terminal-recovery.json'\")")
f=here/'finish-recovered.snapshot.py'; f.write_bytes(text.encode('utf-8')); exec(compile(text,str(f),'exec'),{'__name__':'__main__','__file__':str(f)})
