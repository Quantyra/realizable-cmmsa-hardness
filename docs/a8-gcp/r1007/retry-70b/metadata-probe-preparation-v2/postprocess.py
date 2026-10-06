"""Validate raw metadata and derive separately labelled per-root graphs; no Lean."""
import hashlib,json,sys
from pathlib import Path
raw=Path(sys.argv[1]); destination=Path(sys.argv[2]); destination.mkdir(exist_ok=False)
base=Path(__file__).resolve().parent
spec=json.loads((base/'preparation-status.json').read_bytes())
roots=spec['roots']; focused=[n for n in roots if n.rsplit('.',1)[-1] in ['manuscript_A22_actual','original_HC46_exact','selected_leaf_HC46_original','selected_leaf_failed_zoom_HC46_original']]
assert len(roots)==172 and len(set(roots))==172 and len(focused)==4
nodes={}
for line in raw.read_text(encoding='utf-8').splitlines():
 try:r=json.loads(line)
 except json.JSONDecodeError:continue
 if isinstance(r,dict) and 'name' in r:
  assert r['name'] not in nodes
  if 'type_repr' in r:r['type_repr_sha256']=hashlib.sha256(r['type_repr'].encode()).hexdigest().upper()
  nodes[r['name']]=r
assert all(n in nodes for n in roots)
graphs={}
for label,selected in [('focused-four-consumer',focused),('exact172-native',roots)]:
 reached={};unresolved=[];boundaries={}
 for root in selected:
  seen=set();pending=[root]
  while pending:
   n=pending.pop()
   if n in seen:continue
   seen.add(n)
   if n not in nodes:unresolved.append({'root':root,'constant':n,'reason':'node absent'});continue
   row=nodes[n]
   if row.get('unresolved') or row.get('ownership_unresolved') or row.get('body_unresolved'):unresolved.append({'root':root,'constant':n,'reason':'missing constant/owner/proof'})
   if row.get('project'):pending.extend(row['union_edges'])
   elif not row.get('ownership_unresolved'):boundaries[n]=row.get('module')
  reached[root]=sorted(seen)
 graphs[label]={'roots':selected,'per_root_reachability':reached,'unresolved':unresolved,'library_boundaries':boundaries,'coverage_accepted':False}
summary={'raw_sha256':hashlib.sha256(raw.read_bytes()).hexdigest().upper(),'raw_bytes':raw.stat().st_size,'nodes':nodes,'graphs':graphs,'mathematical_acceptance':False}
(destination/'validated-graphs.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'nodes':len(nodes),'focused_roots':len(focused),'wide_roots':len(roots),'unresolved':[len(g['unresolved']) for g in graphs.values()]}))
