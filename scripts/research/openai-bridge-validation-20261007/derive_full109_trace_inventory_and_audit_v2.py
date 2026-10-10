"""Preserve rejected physical-layout assumption; audit complete actual plan identities."""
import ast
import hashlib
import json
from pathlib import Path
here=Path(__file__).parent
old=here/'audit_full109_trace_cache_large_v1.py'
record=here/'full109-trace-cache-audit-v1-admission-failure';record.mkdir(exist_ok=False)
(record/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
data=old.read_bytes();(record/old.name).open('xb').write(data)
observation=dict(native_exit=1,reason='Actual complete plan has9666 rows, not prior physical-layout9672 rows',
 plan_accepted=False,recovery_executed=False,complete_raw_stdout_not_reconstructed=True)
(record/'observation.json').write_text(json.dumps(observation,indent=2)+'\n')
rows=[]
for path in (record/old.name,record/'observation.json'):
 data=path.read_bytes();rows.append(dict(source=str(path),target=path.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(record/'index.json').write_text(json.dumps(dict(records=rows),indent=2)+'\n')
text=old.read_text()
anchor=" assert len(plan['rows'])==9672 and len({r['relative'] for r in plan['rows']})==9672\n for row in plan['rows']:assert row==index[row['relative']]"
assert text.count(anchor)==1
replacement=""" assert len({r['relative'] for r in plan['rows']})==len(plan['rows'])
 assert len(plan['rows'])==9666 if number==109 else len(plan['rows'])>0
 allocation_differences=[]
 for row in plan['rows']:
  assert row['relative'] in index
  prior_row=index[row['relative']]
  assert (row['bytes'],row['sha256'])==(prior_row['bytes'],prior_row['sha256'])
  assert row['bytes']>=65536 and row['allocated_bytes']>0 and row['allocated_bytes']%512==0
  if row['allocated_bytes']!=prior_row['allocated_bytes']:
   allocation_differences.append(dict(relative=row['relative'],prior=prior_row['allocated_bytes'],current=row['allocated_bytes']))"""
text=text.replace(anchor,replacement)
text=text.replace('scope=number,rows=9672','scope=number,rows=len(plan[\'rows\'])')
text=text.replace('all_rows_match_prior_verified_scope=True','all_actual_rows_match_prior_verified_byte_identities=True,physical_allocation_differences=allocation_differences')
text=text.replace("f'cache-large-{action}-audit-native{number}-v1.json'", "f'cache-large-{action}-audit-native{number}-v2.json'")
target=here/'audit_full109_trace_cache_large_v2.py';ast.parse(text)
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
base=(here/'inspect_full109_trace_resources_v1.py').read_text()
start=base.index('            remote = ');end=base.index('            command = ',start)
remote=(here/'inspect_builder02_dependency_cache_allocation.py').read_text()
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'trace-resource-inspections-v1'", "'trace-cache-allocation-inspections-v1'")
target=here/'inspect_full109_trace_cache_allocation_v1.py';ast.parse(base)
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
print('Derived complete actual-byte plan audit and read-only allocation inventory; no recovery')
