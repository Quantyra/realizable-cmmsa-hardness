"""Use recovered custody without rewriting executed failed receipts."""
import json, runpy, sys, tarfile
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='finish_disk_recovery'); m['configure']()
c=m['common']; run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T023135Z_1fc1ec5c'
supp=json.loads((run/'disk-full-recovery/supplement-terminal.json').read_bytes())
assert supp['vm_terminal_receipt']['status']=='TERMINATED'
archive=run/(run.name+'-recovered-evidence.tar.gz')
with tarfile.open(archive,'r:gz') as tar:
    members=tar.getmembers()
    assert all(not Path(x.name).is_absolute() and '..' not in Path(x.name).parts and not x.issym() and not x.islnk() for x in members)
    target=run/'remote-evidence'
    if not target.exists():
        target.mkdir(); tar.extractall(target,filter='data')
effective={'run':run.name,'capture':'capture-integrated-45','vm_terminal_receipt':supp['vm_terminal_receipt'],'evidence_archive_sha256':supp['custody']['remote_sha256'],'inherited_dirt_preserved':False,'local_compilation':False,'recovery_only':True,'original_zero_byte_terminal_preserved':True}
c.write_new(run/'disk-full-recovery/effective-terminal.json',c.json_bytes(effective))
text=(here/'finish-native.py').read_text(encoding='utf-8')
text=text.replace("run/'terminal.json'","run/'disk-full-recovery/effective-terminal.json'")
text=text.replace("text=text.replace('profiles=axiom_profiles(alltext[3])'", "text=text.replace(\"run/'terminal.json'\",\"run/'disk-full-recovery/effective-terminal.json'\").replace(\"run.name+'-evidence.tar.gz'\",\"run.name+'-recovered-evidence.tar.gz'\")\ntext=text.replace('profiles=axiom_profiles(alltext[3])'")
compile(text,str(here/'finish-disk-recovered.snapshot.py'),'exec')
c.write_new(here/'finish-disk-recovered.snapshot.py',text.encode('utf-8'))
exec(compile(text,str(here/'finish-disk-recovered.snapshot.py'),'exec'),{'__name__':'__main__','__file__':str(here/'finish-disk-recovered.snapshot.py')})
