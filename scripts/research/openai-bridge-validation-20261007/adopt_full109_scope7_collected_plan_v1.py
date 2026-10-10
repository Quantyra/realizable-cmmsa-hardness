"""Admit existing native plan through independently successful read-only collection."""
import base64
import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
from custody_checks import digest
from audit_full109_small_cache_recovery_v3_v8 import main as audit
here=Path(__file__).parent
original=ROOT/'cache-repoint-controls/20261010T093457641991Z'
commands=json.loads((original/'commands.json').read_bytes())
assert len(commands)==7 and [c['native_exit'] for c in commands[:6]]==[0]*6
assert commands[6]['native_exit']==1 and 'scp' in commands[6]['argv']
planner=[c for c in commands if any('--plan' in arg for arg in c['argv'])]
assert len(planner)==1 and planner[0]['native_exit']==0
collected=ROOT/'scope7-readonly-plan-collection-v1/20261010T103750323401Z'
records=json.loads((collected/'commands.json').read_bytes())
assert len(records)==2 and all(c['native_exit']==0 for c in records)
for i,c in enumerate(records):
 assert digest(collected/f'{i}.stdout')==c['stdout_sha256']
 assert digest(collected/f'{i}.stderr')==c['stderr_sha256']
value=json.loads((collected/'inspection.json').read_bytes())
assert value['read_only'] and not value['planner_replayed'] and not value['compiler_invoked']
data=base64.b64decode(value['raw_plan_base64'],validate=True)
assert hashlib.sha256(data).hexdigest().upper()==value['plan_sha256']==digest(original/'plan.json')
destination=ROOT/'cache-repoint-controls/scope7-openssh-collection-v1'
destination.mkdir(exist_ok=False)
for path in sorted(collected.rglob('*')):
 if not path.is_file():continue
 dest=destination/path.relative_to(collected);dest.parent.mkdir(parents=True,exist_ok=True)
 dest.open('xb').write(path.read_bytes())
(destination/'plan.json').open('xb').write(data)
state=json.loads((collected/'0.stdout').read_bytes())
operation=dict(action='plan',VM=state,control_sha256=digest(here/'full109_storage_cache_repoint_v7.py'),
 remote_control='/home/dfredriksen_quantyra_org/full109-storage-cache-repoint-v7',
 local_result=str(destination/'plan.json'),result_sha256=value['plan_sha256'],
 compiler_invoked=False,VM_power_operation=False,accepted=False,
 collection_only=True,original_planner_native_exit=0,original_transfer_native_exit=1,
 original_failure=str(original),original_planner_replayed=False)
(destination/'operation.json').open('x').write(json.dumps(operation,indent=2)+'\n')
audit('plan',7)
print(json.dumps(dict(plan_admitted=True,original_failure_preserved=True,planner_replayed=False)))
