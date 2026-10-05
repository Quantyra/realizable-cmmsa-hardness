"""Retain retry16 diagnostics, frozen-input evidence and permitted successor drift."""
import json, runpy, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
m = runpy.run_path(str(HERE/'controller.py'),run_name='finish_recovery_import')
gates=json.loads((HERE/'offline-gates.json').read_bytes())
m['configure'](gates['candidate_hashes'])
common=m['common']; PACKAGE=m['PACKAGE']; OWNED=m['OWNED']
run=PACKAGE/'runs'/'cmmsa_a8_output_20261005T191951Z_7ea37ffb'
terminal=json.loads((run/'terminal.json').read_bytes())
assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
m['old'].old.verify_custody(json.loads((run/'custody.json').read_bytes()))
text=(PACKAGE/'retry-15/finish.snapshot.py').read_text(encoding='utf-8')
text=text.replace("PACKAGE/'retry-15'","PACKAGE/'retry-16'")
text=text.replace('if SOURCE in h or CHECKS in h','if any(n in h for n in OWNED)')
text=text.replace('assert all(file_sha(REPO/n)==h for n,h in FROZEN.items())',"write_new(run/'successor-state-after.json',json_bytes({'frozen_offer':FROZEN,'current_owned':{n:file_sha(REPO/n) for n in OWNED},'permitted_successor_custody':'retry-16/successor-support-offer/custody.json','frozen_capture_unchanged':True}))")
text=text.replace('assert file_sha(REPO/SOURCE)==manifest[\'offered_identities\'][SOURCE]',"assert file_sha(capture/'inputs'/SOURCE)==manifest['offered_identities'][SOURCE]")
text=text.replace("'source_unchanged':True","'frozen_source_unchanged':True,'mutable_successor_authoring_permitted':True")
text=text.replace("'inherited_dirt_preserved':False","'inherited_dirt_preserved':terminal['inherited_dirt_preserved']")
text=text.replace('Candidate hashes, HEAD, origin/main, and unstaged index verified unchanged.', 'Frozen compiled input hashes, HEAD, origin/main, and unstaged index verified unchanged; permitted mutable successor authoring recorded separately.')
text=text.replace('Inherited worktree drift is recorded separately in retry-14/inherited-drift.json; it was not repaired or hidden.', 'Historical retry14/retry15 red drift audits preserved; current inherited preservation result recorded in terminal.json. Owned successor changes are distinct from frozen compiled bytes.')
common.write_new(HERE/'finish-recovery.snapshot.py',text)
sys.argv=['finish',run.name,'retry-16/recovery-report']
exec(compile(text,str(HERE/'finish-recovery.snapshot.py'),'exec'),{'__name__':'__main__','OWNED':OWNED})
report=json.loads((HERE/'recovery-report.json').read_bytes())
warnings=json.loads((run/'warning-classification.json').read_bytes())
counts=[common.diagnostic_counts((run/'remote-evidence'/f'stage-{i}.stdout').read_text(encoding='utf-8'),(run/'remote-evidence'/f'stage-{i}.stderr').read_text(encoding='utf-8')) for i in range(4)]
profiles=report['axiom_profiles']
axiom_ok=all(n in profiles and set(profiles[n])<=common.STANDARD_AXIOMS for n in common.REQUESTED_AXIOMS)
green=all(s['exit']==0 for s in report['stages']) and all(c['errors']==c['unsolved_goals']==0 for c in counts) and all(not s['owned_above_frozen_baseline'] and not s['inherited_above_frozen_baseline'] for s in warnings['stages']) and axiom_ok
common.write_new(HERE/'recovery-decision.json',common.json_bytes({'run':run.name,'capture':'capture-retry-16','compiler_attempt':'GREEN development' if green else 'RED development','stage_exits':[s['exit'] for s in report['stages']],'diagnostics':counts,'warnings':warnings,'axiom_profiles':profiles,'axiom_gate':axiom_ok,'candidate_hashes':gates['candidate_hashes'],'custody':json.loads((run/'custody.json').read_bytes()),'terminal':terminal,'independently_terminated':json.loads((run/'independent-termination/receipt.json').read_bytes()),'legacy_zero_total_audit':json.loads((run/'audit.json').read_bytes()),'bounded_increment':'UNACCEPTED count 2','S3132':'PARTIAL','fullS3137':'INCOMPLETE','helper_credit':0,'roadmap_credit':0}))
print('RECOVERY DECISION',green,counts,flush=True)
