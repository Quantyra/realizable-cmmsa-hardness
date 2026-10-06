"""Pin Root's complete seventeen-file review custody for focused Git preservation."""
import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; repo=p.parents[3]
scope=json.loads((p/'authorized-disjoint-review-paths.json').read_bytes())
extra=json.loads((p/'review-closeout-paths.json').read_bytes())
names=list(scope['immutable_packet_sha256'])+scope['mutable_paths']+extra['additional_mutable_paths']
assert len(names)==17 and len(set(names))==17
pins={n:hashlib.sha256((repo/n).read_bytes()).hexdigest().upper() for n in names}
assert all(pins[n]==h for n,h in scope['immutable_packet_sha256'].items())
with (p/'completed-review-file-pins.json').open('x',encoding='utf-8') as f:json.dump({'files':pins,'root_reported_complete_stable':True,'root_acceptance_scope':'original full A8 OUTPUT-Q transport endpoint only','helper_credit':0,'S3132':'PARTIAL','S3137':'INCOMPLETE','full_manuscript_A11_acceptance':False},f,indent=2)
print('Seventeen exact stable Root review files pinned; no Git writes')
