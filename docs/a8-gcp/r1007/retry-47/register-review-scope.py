"""Register exact disjoint review writes and pin immutable frozen46 packet."""
import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; repo=p.parents[3]
base='docs/reviews/full-original-a8-20261006T0316Z'
mutable=[base+'/'+prefix+suffix for prefix in ['proof-adversarial','complexity-theory','non-claims-boundary'] for suffix in ['-command.json','-stdout.json','-stderr.txt','-terminal.json']]
immutable={base+'/'+name:hashlib.sha256((repo/base/name).read_bytes()).hexdigest().upper() for name in ['common-source-packet.txt','scope.json','run-review.py']}
value={'authorized_by':'Root exact bounded top-level review instructions','mutable_paths':mutable,'immutable_packet_sha256':immutable,'source_or_compiler_scope_changed':False,'review_outputs_not_formal_dependencies':True,'inherited_tracked_dirt_and_untracked_Lean_preserved':True,'untracked_nonLean_review_directory_retained_in_status_baseline':True}
with (p/'authorized-disjoint-review-paths.json').open('x',encoding='utf-8') as f:json.dump(value,f,indent=2)
print(json.dumps({'registered_mutable_paths':len(mutable),'immutable_packet_files':len(immutable),'formal_scope_changed':False}))
