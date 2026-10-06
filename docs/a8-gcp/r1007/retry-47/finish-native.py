"""Full fourteen-target diagnostic, fresh-axiom and custody closeout."""
import runpy,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
m=runpy.run_path(str(HERE/'controller.py'),run_name='finish47_import'); m['configure']()
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T030313Z_2f112c58'
terminal=json.loads((run/'terminal.json').read_bytes()); assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
d=run/'remote-evidence'; cache=json.loads((d/'verified-cache-provenance.json').read_bytes()); objects=json.loads((d/'object-after.json').read_bytes())
comparison={'cache_objects':len(cache['objects']),'changed':[n for n,h in cache['objects'].items() if objects.get(n)!=h],'compiler_equal':json.loads((d/'compiler-identity.json').read_bytes())==cache['compiler'],'packages_equal':json.loads((d/'package-source-hashes.json').read_bytes())==cache['package_sources'],'core_equal':json.loads((d/'core-source-hashes.json').read_bytes())==cache['core_sources']}
assert not comparison['changed'] and comparison['compiler_equal'] and comparison['packages_equal'] and comparison['core_equal']
m['common'].write_new(run/'cache-comparison.json',m['common'].json_bytes(comparison))
text=(m['PACKAGE']/'retry-15/finish.snapshot.py').read_text(encoding='utf-8')
text=text.replace('from runner import Control','from runner import Control\nfrom common import STANDARD_AXIOMS, REQUESTED_AXIOMS')
text=text.replace('assert all(file_sha(REPO/n)==h for n,h in FROZEN.items())','assert all(file_sha(capture/\'inputs\'/n)==FROZEN[n] for n in OWNED)')
text=text.replace("assert file_sha(REPO/SOURCE)==manifest['offered_identities'][SOURCE]","assert file_sha(capture/'inputs'/SOURCE)==manifest['offered_identities'][SOURCE]")
text=text.replace('if SOURCE in h or CHECKS in h','if any(n in h for n in OWNED)')
text=text.replace("PACKAGE/'retry-15'","PACKAGE/'retry-47'")
text=text.replace('profiles=axiom_profiles(alltext[3])','profiles=axiom_profiles(alltext[3])\ngreen=green and all(n in profiles and set(profiles[n])<=STANDARD_AXIOMS for n in REQUESTED_AXIOMS)')
text=text.replace('Candidate hashes, HEAD, origin/main, and unstaged index verified unchanged.','Immutable input hashes, HEAD, origin/main, and unstaged index verified unchanged; mutable successor custody remains separate.')
text=text.replace("'source_unchanged':True","'frozen_source_unchanged':True,'mutable_successors_permitted':True")
text=text.replace("'inherited_dirt_preserved':False","'inherited_dirt_preserved':terminal['inherited_dirt_preserved']")
text=text.replace('Evidence left uncommitted.','Focused current-turn preservation commit follows settlement.')
text=text.replace('Endpoint `a8_output_q_le_actual_predecessor_sum` remains open.','Original A8 endpoint, weighted A11 hS and final allspaces A7 remain unaccepted pending full native and three-lens gates.')
text=text.replace('for i in range(4):\n    code=', 'for i in range(7):\n    code=')
text=text.replace('axiom_profiles(alltext[3])','axiom_profiles(alltext[6])')
(HERE/'finish-native.snapshot.py').write_bytes(text.encode())
sys.argv=['finish',run.name,'retry-47/native-report']
exec(compile(text,str(HERE/'finish-native.snapshot.py'),'exec'),{'__name__':'__main__','OWNED':m['OWNED']})
