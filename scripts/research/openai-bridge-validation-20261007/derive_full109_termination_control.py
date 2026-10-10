"""Bind existing exact-VM custody-before-stop control to immutable Full109."""
from pathlib import Path
import ast
import json
import hashlib
here=Path(__file__).parent
source=here/'terminate_builder02_after_custody.py'
before=source.read_text()
anchor='from builder02_controller import ROOT, VM, VM_ID, audit_terminal, context, local_gates'
assert before.count(anchor)==1
after=before.replace(anchor,'from full109_builder02_controller import ROOT, VM, VM_ID, audit_terminal, context, local_gates')
ast.parse(after)
target=here/'terminate_full109_builder02_after_custody.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(after)
assert after.replace('from full109_builder02_controller import','from builder02_controller import')==before
record=dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest().upper(),
 target_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),
 change='Only controller import rebound to Full109',custody_before_stop_preserved=True,
 exact_vm_and_quiescence_and_independent_termination_preserved=True,cloud_operation_executed=False)
(here/'full109-termination-control-derivation.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
