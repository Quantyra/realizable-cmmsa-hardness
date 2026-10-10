"""Derive read-only complete row-state inspection; preserve original inspector."""
from pathlib import Path
import hashlib
import json

here = Path(__file__).parent
source = here/'inspect_full109_recovery_via_openssh.py'
data = source.read_text()
anchor = 'print(json.dumps(result))\n"""'
assert data.count(anchor) == 1
replacement = '''
assert not pids and not receipt.exists(), 'Existing final receipt/process; inspect separately'
plan_path=folder/'plan.json';plan_bytes=plan_path.read_bytes();plan=json.loads(plan_bytes)
partial_bytes=partial.read_bytes();part=json.loads(partial_bytes)
assert part['applied']==plan['rows'][:len(part['applied'])]
assert len(plan['rows'])==19233
old=Path(plan['old_root']);canonical=Path(plan['canonical_root'])
assert old==home/'cmmsa_a8_output_20261010T081548Z_260bb38e/.lake/packages'
assert canonical==home/'cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
states=[]
for index,row in enumerate(plan['rows']):
 rel=Path(row['relative']);assert not rel.is_absolute() and '..' not in rel.parts
 path=old/rel;dest=canonical/rel;backup=path.with_name(path.name+'.full95-repoint-backup')
 assert dest.resolve(strict=True).is_relative_to(canonical)
 assert dest.stat().st_size==row['bytes']
 assert hashlib.sha256(dest.read_bytes()).hexdigest().upper()==row['sha256']
 assert not backup.exists() and not backup.is_symlink(), 'Boundary backup requires separate inspection'
 if path.is_symlink():
  assert path.readlink()==dest and path.resolve(strict=True)==dest.resolve(strict=True)
  state='completed-symlink'
 else:
  assert path.resolve(strict=True).is_relative_to(old)
  info=path.stat();assert info.st_nlink==1 and info.st_size==row['bytes']
  assert hashlib.sha256(path.read_bytes()).hexdigest().upper()==row['sha256']
  state='remaining-regular'
 if index<len(part['applied']):assert state=='completed-symlink'
 states.append(state)
completed=states.count('completed-symlink')
assert states==['completed-symlink']*completed+['remaining-regular']*(len(states)-completed)
assert len(part['applied'])<=completed<=len(part['applied'])+1
result.update(plan_sha256=hashlib.sha256(plan_bytes).hexdigest().upper(),
 partial_sha256=hashlib.sha256(partial_bytes).hexdigest().upper(),
 recorded_applied_rows=len(part['applied']),verified_completed_rows=completed,
 remaining_rows=len(states)-completed,all_row_states_verified=True,
 boundary_backups_present=False,partial_receipt=part,row_states=states,
 execute_once=json.loads((folder/'execute-once.json').read_bytes()))
print(json.dumps(result))
"""'''
data=data.replace(anchor,replacement)
data=data.replace("'openssh-recovery-inspections'", "'openssh-partial-inspections-v2'")
old="print(json.dumps(dict(folder=str(folder), inspection=result, host_key_fingerprint=fingerprint)), flush=True)"
new="print(json.dumps(dict(folder=str(folder), inspection={k:v for k,v in result.items() if k not in ('partial_receipt','row_states')}, host_key_fingerprint=fingerprint)), flush=True)"
assert data.count(old)==1
data=data.replace(old,new)
target=here/'inspect_full109_partial_via_openssh_v2.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(data)
record=dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest().upper(),
 target_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),
 purpose='Read-only exhaustive partial recovery row-state audit', recovery_executed=False)
(here/'full109-partial-inspector-v2-derivation.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
