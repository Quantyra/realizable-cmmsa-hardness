"""Offline diagnostic extraction plus independent GCP termination observation. No compiler or Git writes."""
from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
import json,re,subprocess,sys
from common import PACKAGE,REPO,SOURCE,CHECKS,FROZEN,file_sha,write_new,json_bytes,inherited_now,inherited_status_now,axiom_profiles
from runner import Control
from common import STANDARD_AXIOMS, REQUESTED_AXIOMS

run=PACKAGE/'runs'/sys.argv[1] if len(sys.argv)>1 else next((PACKAGE/'runs').iterdir())
report_stem=sys.argv[2] if len(sys.argv)>2 else 'diagnostic-report'
terminal=json.loads((run/'terminal.json').read_bytes())
assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
assert terminal['evidence_archive_sha256']==file_sha(run/(run.name+'-evidence.tar.gz'))
receipt=run/'remote-evidence'
capture=PACKAGE/'captures'/terminal['capture']
manifest=json.loads((capture/'manifest.json').read_bytes())
FROZEN=manifest["offered_identities"]
expected={n:r['sha256'] for n,r in manifest['project_sources'].items()}
expected.update({n:r['sha256'] for n,r in manifest['configs'].items()})
assert json.loads((receipt/'source-before.json').read_bytes())==expected
assert json.loads((receipt/'source-after.json').read_bytes())==expected
assert all(file_sha(capture/'inputs'/n)==FROZEN[n] for n in OWNED)
before=json.loads((capture/'heads-before.json').read_bytes())
heads={'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO).decode().strip(),
       'origin_main':subprocess.check_output(['git','rev-parse','origin/main'],cwd=REPO).decode().strip(),
       'index':subprocess.check_output(['git','diff','--cached','--name-only'],cwd=REPO).decode().splitlines()}
assert heads['head']==before['head'] and heads['origin_main']==before['origin_main'] and not heads['index']
assert file_sha(capture/'inputs'/SOURCE)==manifest['offered_identities'][SOURCE]
# Drift retained in retry-14/inherited-drift.json; no historical rewrite.
write_new(run/'git-preservation-after.json',json_bytes(heads))
observation=run/'independent-termination'; observation.mkdir()
control=Control(observation)
final=control.describe(); assert final['status']=='TERMINATED'
write_new(observation/'receipt.json',json_bytes({'utc':datetime.now(timezone.utc).isoformat(),'state':final,'independent':True}))

def warnings(root,index):
    headers=Counter()
    for suffix in ['stdout','stderr']:
        for line in (root/f'stage-{index}.{suffix}').read_text(encoding='utf-8',errors='replace').splitlines():
            if re.match(r'^(?:warning\s*:|[^\s].*:\d+:\d+:\s*warning\s*:)',line):
                headers[re.sub(r'/home/dfredriksen_quantyra_org/cmmsa_[^/]+/','<RUN>/',line)]+=1
    return headers
seal=json.loads((PACKAGE/'warning-baseline-seal.json').read_bytes())
assert all(file_sha(PACKAGE/n)==h for n,h in seal['files'].items())
baseline=Counter()
for i in range(4): baseline |= warnings(PACKAGE/'warning-baseline',i)
stages=[]; diagnostics=[]; alltext=[]
source_lines=(capture/'source.lean.snapshot').read_text(encoding='utf-8').splitlines()
for i in range(8):
    code=int((receipt/f'stage-{i}.native-exit').read_text())
    text='\n'.join((receipt/f'stage-{i}.{s}').read_text(encoding='utf-8',errors='replace') for s in ['stdout','stderr'])
    alltext.append(text)
    rows=warnings(receipt,i)
    owned=Counter({h:c for h,c in rows.items() if any(n in h for n in OWNED)})
    inherited=rows-owned
    stages.append({'index':i,'exit':code,'warning_headers':sum(rows.values()),'owned_headers':dict(owned),'owned_above_frozen_baseline':dict(owned-baseline),'retained_baseline_headers':dict(rows & baseline),'inherited_dependency_headers':dict(inherited),'inherited_above_frozen_baseline':dict(inherited-baseline)})
    lines=text.splitlines()
    for j,line in enumerate(lines):
        match=re.match(r'^(?:error:\s*)?(.+\.lean):(\d+):(\d+): (?:error:\s*)?(.*)',line)
        if 'warning:' in line or not ('error:' in line): continue
        if not match: continue
        end=next((k for k in range(j+1,len(lines)) if re.match(r'^(.+\.lean:\d+:\d+: (?:error|warning):|error:|warning:|[✖✔⚠])',lines[k])),len(lines))
        file,num,col,message=match.groups(); num=int(num)
        context=[]
        relative=next((n for n in manifest['project_sources'] if file.endswith(n)),None)
        if relative:
            context_lines=(capture/'inputs'/relative).read_text(encoding='utf-8').splitlines()
            context=[f'{k+1}: {context_lines[k]}' for k in range(max(0,num-3),min(len(context_lines),num+2))]
        diagnostics.append({'stage':i,'file':file,'line':num,'column':int(col),'message':message,'exact_block':'\n'.join(lines[j:end]),'candidate_context':context})
write_new(run/'warning-classification.json',json_bytes({'policy':'Inherited warnings retained separately as S3137 certification-policy evidence; no suppression or cleanup. No acceptance credit.','baseline_union_headers':sum(baseline.values()),'seal_sha256':file_sha(PACKAGE/'warning-baseline-seal.json'),'stages':stages}))
write_new(run/'lean-diagnostics.json',json_bytes(diagnostics))
write_new(run/'lean-diagnostics.txt','\n\n'.join(d['exact_block']+'\n\nCandidate context:\n'+'\n'.join(d['candidate_context']) for d in diagnostics))
green=all(s['exit']==0 and not s['owned_above_frozen_baseline'] and not s['inherited_above_frozen_baseline'] for s in stages)
profiles=axiom_profiles(alltext[7])
green=green and all(n in profiles and set(profiles[n])<=STANDARD_AXIOMS for n in REQUESTED_AXIOMS)
label='development-compile green / not accepted' if green else 'compiler-attempt red / bounded increment not accepted / S3132 partial / S3137 incomplete'
report={'run':run.name,'label':label,'roadmap_credit':0,'accepted':False,'stages':[{'index':s['index'],'exit':s['exit'],'warning_headers':s['warning_headers']} for s in stages],'candidate_hashes':FROZEN,'vm_final_status':final['status'],'frozen_source_unchanged':True,'mutable_successors_permitted':True,'inherited_dirt_preserved':terminal['inherited_dirt_preserved'],'git_writes':False,'local_compilation':False,'diagnostic_count':len(diagnostics),'axiom_profiles':profiles,'input_archive_sha256':manifest['files']['input-archive.tar.gz']['sha256'],'cloud_evidence_archive_sha256':terminal['evidence_archive_sha256'],'dependency_provenance':dict(Counter(r['basis'] for r in manifest['project_sources'].values())),'started_utc':(receipt/'started.utc').read_text().strip(),'finished_utc':(receipt/'terminal.utc').read_text().strip()}
write_new(PACKAGE/(report_stem+'.json'),json_bytes(report))
body=f'# S3132 r1007 diagnostic compiler result\n\n{label}. Zero roadmap credit. Original A8 endpoint, weighted A11 hS and final allspaces A7 remain unaccepted pending full native and three-lens gates.\n\nRun `{run.name}`; GCP instance `8337954477286097405`; stages '+ '/'.join(str(s['exit']) for s in stages)+'. Source bytes unchanged; no local compiler, source repair, staging, commit, or push.\n\n'
body+='Candidate SHA-256:\n\n'+ '\n'.join(f'- `{n}`: `{h}`' for n,h in FROZEN.items())+'\n\n'
body+='Exact diagnostics with context: `'+str((run/'lean-diagnostics.txt').relative_to(PACKAGE)).replace('\\','/')+'`. Raw compiler logs, command arrays, timestamps, native exits, source/object inventories and verified cloud archive are under this run. Stages with exit 125 were skipped following prior-stage failure, per the established protocol.\n\n'
body+='Warning headers by stage: '+ '/'.join(str(s['warning_headers']) for s in stages)+'. `warning-classification.json` preserves owned/inherited headers and comparisons with the sealed baseline. Legacy zero-total audit remains separate.\n\n'
body+='Project baseline provenance: '+json.dumps(report['dependency_provenance'])+'. Exact local candidate overlays; every dependency basis and hash is in the capture manifest. The prior HEAD prerequisite failure and the correction to the established r1005 closure are retained separately.\n\n'
body+='VM `TERMINATED`, proved by the runner and a fresh independent GCP describe after archive custody. Immutable input hashes, HEAD, origin/main, and unstaged index verified unchanged; mutable successor custody remains separate. Inherited worktree drift is recorded separately in retry-14/inherited-drift.json; it was not repaired or hidden. Focused current-turn preservation commit follows settlement.\n'
if diagnostics: body+='\nFirst actionable diagnostics:\n\n'+ '\n'.join(f'- `{Path(d["file"]).name}:{d["line"]}:{d["column"]}`: {d["message"]}' for d in diagnostics[:5])+'\n'
if green: body+='\nAxiom profiles:\n\n```json\n'+json.dumps(profiles,indent=2)+'\n```\n'
write_new(PACKAGE/(report_stem+'.md'),body)
inventory={p.relative_to(PACKAGE).as_posix():file_sha(p) for root in [run,capture,PACKAGE/'retry-54'] for p in root.rglob('*') if p.is_file()}
write_new(PACKAGE/(report_stem+'-evidence-files.sha256.json'),json_bytes(inventory))
print(json.dumps(report,indent=2))
