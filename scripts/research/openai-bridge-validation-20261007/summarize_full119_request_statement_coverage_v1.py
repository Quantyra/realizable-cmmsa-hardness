from pathlib import Path
import json,re,hashlib
H=Path(__file__).resolve().parent
ROOT=Path('C:/Users/dfred/.quantyra/builder02/full119-exact-real-complex-operators-repair9-resource02')
Q=ROOT/'checks/20261012T074047331828Z/qualified-native/cmmsa_a8_output_20261012T074255Z_4527aeb2'
def main():
 m=json.loads((ROOT/'capture-manifest.json').read_bytes());req=m['requested_axioms'];assert len(req)==len(set(req))==347;profiles={}
 for i in range(7):
  for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(Q/'remote-evidence'/f'stage-{i}.stdout').read_text()):
   a=sorted(x.strip() for x in v.replace('\n',' ').split(',') if x.strip());assert n not in profiles or profiles[n]==a;profiles[n]=a
 assert len(profiles)==357 and all(n in profiles and set(profiles[n])<={'propext','Classical.choice','Quot.sound'} for n in req)
 orig=json.loads((Q/'resource-current-axiom-owner-identities.json').read_bytes());owners={x['qualified']:x for x in orig['requests']};rows=[];amb=[]
 sources={rel:(H/'full119-review-source-capsule-v1'/rel).read_bytes().decode('utf8') for rel in m['project_sources']}
 for n in req:
  short=n.rsplit('.',1)[-1];candidates=[]
  for rel,text in sources.items():
   for a in re.finditer(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev)\s+'+re.escape(short)+r'\b',text):
    line=text[:a.start()].count('\n')+1
    if n in owners and (rel!=owners[n]['owner_file'] or line!=owners[n]['current_owner_line']):continue
    tail=text[a.start():];stop=tail.find(':=');header=tail[:stop if stop>=0 else tail.find('\n')]
    candidates.append(dict(source=rel,source_sha256=m['project_sources'][rel]['sha256'],line=line,declaration_header_sha256=hashlib.sha256(header.encode()).hexdigest().upper(),declaration_header=header))
  if len(candidates)!=1:amb.append(dict(request=n,candidates=candidates))
  rows.append(dict(request=n,axioms=profiles[n],source_statement_candidates=candidates,unique_source_owner=len(candidates)==1))
 w=json.loads((Q/'warning-classification.json').read_bytes());j=dict(run='cmmsa_a8_output_20261012T074255Z_4527aeb2',requested347_exact_name_axiom_coverage=True,reported_profiles=357,additional_reported_profiles=sorted(set(profiles)-set(req)),requests=rows,ambiguous_source_statement_bindings=amb,unique_statement_owners=sum(x['unique_source_owner'] for x in rows),statement_binding_status='Exact source declaration headers; kernel statement-equivalence and mathematical body review remain incomplete',stage_exits=[0]*7,new_owned_warning_counts=[sum(s['new_owned_headers'].values()) for s in w['stages']],owned_above_baseline_counts=[sum(s['owned_above_frozen_baseline'].values()) for s in w['stages']],inherited_above_baseline_counts=[sum(s['inherited_above_frozen_baseline'].values()) for s in w['stages']],qualification_green=False,historical_zero_warning_red_preserved=True,accepted=False)
 p=H/'full119-request-statement-axiom-warning-coverage-v1.json';p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest().upper(),unique_statement_owners=j['unique_statement_owners'],ambiguous=len(amb))))
if __name__=='__main__':main()
