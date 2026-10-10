from pathlib import Path
import hashlib
import json
import ast
here=Path(__file__).parent
helper=here/'full109_scope3_remaining_only_v1.py'
source_sha=hashlib.sha256((here/'full109_storage_cache_repoint_v3.py').read_bytes()).hexdigest().upper()
data=helper.read_text().replace("CONTROL=HOME/'full109-storage-cache-repoint-v3'", "CONTROL=HOME/'full109-storage-cache-repoint-v3'\nSOURCE_SHA="+repr(source_sha))
helper.write_text(data,encoding='utf-8',newline='\n');ast.parse(data)
base=(here/'inspect_full109_recovery_via_openssh.py').read_text()
start=base.index('            remote = """');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(data)+'\n'+base[end:]
base=base.replace("'openssh-recovery-inspections'", "'scope3-remaining-only-controls-v1'")
base=base.replace('inspection=result, host_key_fingerprint=fingerprint','inspection={k:v for k,v in result.items() if k != "receipt"}, host_key_fingerprint=fingerprint')
target=here/'continue_full109_scope3_via_openssh_v1.py';assert not target.exists()
target.write_text(base,encoding='utf-8',newline='\n');ast.parse(base)
record=dict(original_source_sha256=source_sha,
 helper_sha256=hashlib.sha256(helper.read_bytes()).hexdigest().upper(),
 controller_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),
 completed_rows=18781,remaining_rows=452,original_execute_replayed=False)
(here/'full109-scope3-remaining-only-derivation-v1.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
