"""Bind unchanged full resource gates to independently audited interrupted scope3."""
from pathlib import Path
import ast
import hashlib
import json
here=Path(__file__).parent
source=here/'resume_full109_staging_after_storage_v3.py'
text=source.read_text()
anchor="'/home/dfredriksen_quantyra_org/full109-storage-cache-repoint-v3', "
assert text.count(anchor)==1
text=text.replace(anchor,'')
anchor="    for number in range(3,9): audit_small_recovery('receipt',number)"
assert text.count(anchor)==1
text=text.replace(anchor,"    from audit_full109_scope3_remaining_only_v1 import main as audit_interrupted\n    audit_interrupted()\n    for number in range(4,9): audit_small_recovery('receipt',number)")
text=text.replace('second_start=False,compiler_invoked=False',
 'original_staging_replayed=False,separate_readonly_recovery_boot=True,compiler_invoked=False')
target=here/'resume_full109_staging_after_storage_v4.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
ast.parse(text)
record=dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest().upper(),
 target_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),
 changes=['Scope3 checked by complete interrupted-state/remaining-only audit instead of nonexistent original-success receipt',
 'Accurate separate recovery boot disclosure'],required_scopes=[1,3,4,5,6,7,8],
 disk_gib=40,memory_gib=48,local_reserve_mib=1536,compiler_invoked=False)
(here/'full109-staging-resume-v4-derivation.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
