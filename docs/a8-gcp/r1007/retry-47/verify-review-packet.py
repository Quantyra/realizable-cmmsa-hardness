"""Verify disjoint immutable review packet before launch without changing it."""
import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; repo=p.parents[3]
scope=json.loads((p/'authorized-disjoint-review-paths.json').read_bytes())
assert len(scope['mutable_paths'])==12
assert all(hashlib.sha256((repo/n).read_bytes()).hexdigest().upper()==h for n,h in scope['immutable_packet_sha256'].items())
with (p/'review-packet-prelaunch.json').open('x',encoding='utf-8') as f:json.dump({'immutable_packet_verified':True,'mutable_output_paths':scope['mutable_paths'],'formal_source_scope_unchanged':True},f,indent=2)
print('Immutable review packet verified; only twelve disjoint output paths mutable')
