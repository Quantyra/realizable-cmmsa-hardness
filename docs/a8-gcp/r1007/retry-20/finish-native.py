"""Retain native diagnostics and independently settled resource proof."""
import runpy,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
m=runpy.run_path(str(HERE/'controller.py'),run_name='finish_native_import'); m['configure']()
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261005T204004Z_25170909'
terminal=json.loads((run/'terminal.json').read_bytes())
terminal['vm_terminal_receipt']=json.loads((run/'settlement-recovery/supplement-terminal.json').read_bytes())['vm_terminal_receipt']
assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
text=(m['PACKAGE']/'retry-15/finish.snapshot.py').read_text(encoding='utf-8')
text=text.replace("terminal=json.loads((run/'terminal.json').read_bytes())","terminal=json.loads((run/'terminal.json').read_bytes()); terminal['vm_terminal_receipt']=json.loads((run/'settlement-recovery/supplement-terminal.json').read_bytes())['vm_terminal_receipt']")
text=text.replace('assert all(file_sha(REPO/n)==h for n,h in FROZEN.items())','assert all(file_sha(capture/\'inputs\'/n)==FROZEN[n] for n in OWNED)')
text=text.replace("assert file_sha(REPO/SOURCE)==manifest['offered_identities'][SOURCE]","assert file_sha(capture/'inputs'/SOURCE)==manifest['offered_identities'][SOURCE]")
text=text.replace('if SOURCE in h or CHECKS in h','if any(n in h for n in OWNED)')
text=text.replace("PACKAGE/'retry-15'","PACKAGE/'retry-20'")
text=text.replace('Candidate hashes, HEAD, origin/main, and unstaged index verified unchanged.','Immutable captured input hashes, HEAD, origin/main, and unstaged index verified unchanged; authorized mutable successor paths preserved separately.')
text=text.replace("'source_unchanged':True","'frozen_source_unchanged':True,'mutable_successors_permitted':True")
text=text.replace("'inherited_dirt_preserved':False","'inherited_dirt_preserved':terminal['inherited_dirt_preserved']")
text=text.replace('Evidence left uncommitted.','Focused current-turn preservation commit follows settlement.')
(HERE/'finish-native.snapshot.py').write_bytes(text.encode('utf-8'))
sys.argv=['finish',run.name,'retry-20/native-report']
exec(compile(text,str(HERE/'finish-native.snapshot.py'),'exec'),{'__name__':'__main__','OWNED':m['OWNED']})
