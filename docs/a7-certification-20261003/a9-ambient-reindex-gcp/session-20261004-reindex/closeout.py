"""Offline bounded report, hash inventory and preservation check. No Git writes."""
from pathlib import Path
import json, hashlib, sys
from common import inherited_now, file_sha, SOURCE, CHECKS

p=Path(__file__).resolve().parent
run=p/'runs'/sys.argv[1]
audit=json.loads((run/'prospective-audit.json').read_bytes())
legacy=json.loads((run/'audit.json').read_bytes())
manifest=json.loads((run/'manifest.json.snapshot').read_bytes())
terminal=json.loads((run/'terminal.json').read_bytes())
proofs=[]
for folder in run.glob('independent-terminal-*'):
    receipt=folder/'receipt.json'
    if receipt.exists() and json.loads(receipt.read_bytes()).get('terminated_verified'):
        proofs.append(str(receipt.relative_to(p)))
assert proofs,'Independent terminal proof required'
capture=p/'captures'/audit['run'].replace(audit['run'],legacy['capture'])
before=json.loads((capture/'inherited-files-before.json').read_bytes())
assert inherited_now()==before,'Unrelated dirty file drift'
assert all(file_sha(p.parents[3]/r)==manifest['offered_identities'][r] for r in [SOURCE,CHECKS])
attempts=[]
for r in sorted((p/'runs').iterdir()):
    if not (r/'audit.json').exists(): continue
    a=json.loads((r/'audit.json').read_bytes())
    t=json.loads((r/'terminal.json').read_bytes())
    attempts.append({'run':r.name,'stage_results':a['stage_results'],
                     'vm_status':t['vm_terminal_receipt']['status'],
                     'evidence_archive_sha256':t['evidence_archive_sha256']})
report={'owning_story':'S3132','bounded_increment':'analytic A9 actual-fiber reindexing/charge',
        'bounded_acceptance_green':audit['green'],'legacy_zero_total_warning_green':legacy['green'],
        'source_sha256':audit['source_sha256'],'checks_sha256':audit['checks_sha256'],
        'manifest_sha256':file_sha(run/'manifest.json.snapshot'),
        'input_archive_sha256':manifest['files']['input-archive.tar.gz']['sha256'],
        'evidence_archive_sha256':terminal['evidence_archive_sha256'],
        'run':run.name,'stage_results':legacy['stage_results'],
        'remote_exits':{n:int((run/'remote-evidence'/n).read_text()) for n in ['native-exit','aggregate.native-exit','finish.native-exit']},
        'axiom_profiles':legacy.get('axiom_profiles'),
        'warning_policy':audit,'attempts':attempts,
        'independent_terminal_proofs':proofs,'vm_id':terminal['vm_terminal_receipt']['id'],
        'vm_last_stop':terminal['vm_terminal_receipt']['lastStopTimestamp'],
        'inherited_files_preserved':True,'local_lean_lake_elan_execution':False,
        'repairs':'Compiler/statement only; graph factor restored before first build; routine equality, destructuring, namespace and tactic repairs thereafter.',
        'new_carriers_or_premises':0,'helper_development_increments':0,
        'theorem_weakening':False,'three_lens_reviews':'NOT RUN as instructed',
        'S3137':'INCOMPLETE; all inherited warnings retained without suppression',
        'full_manuscript_or_story_closeout_claim':False,
        'git_status':'Pending selective owner commit and push, conditional on green acceptance'}
(p/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
lines=['S3132 bounded analytic A9 reindexing/charge compiler closeout','',
       f"Acceptance: {'GREEN' if audit['green'] else 'RED'}. Legacy zero-total-warning audit: {'GREEN' if legacy['green'] else 'RED'}, separately retained.",
       f"Run: {run.name}",f"Source SHA-256: {audit['source_sha256']}",f"Checks SHA-256: {audit['checks_sha256']}",
       f"Manifest SHA-256: {report['manifest_sha256']}",f"Input archive SHA-256: {report['input_archive_sha256']}",
       f"Cloud evidence archive SHA-256: {report['evidence_archive_sha256']}",'']
for row in legacy['stage_results']:
    lines.append(f"Stage {row['index']} {row['name']}: exit {row['native_exit']}; legacy diagnostic warnings {row['warnings']}; errors {row['errors']}; unsolved goals {row['unsolved_goals']}.")
lines += ['',f"Remote terminal/aggregate/finish: {report['remote_exits']}",
          f"Principal axiom profiles: {json.dumps(report['axiom_profiles'],sort_keys=True)}",'',
          'Original warning debt: 748 inherited dependency diagnostics plus 13 pre-existing ambient owned style diagnostics, retained as S3137 debt.',
          'The A8 energy imports require 37 additional unchanged dependencies: 343 further diagnostic occurrences (329 actual warning headers). Frozen from the failed first cloud run before its successor; original baseline did not regress. Legacy counts include warning text inside multiline hints.',
          f"New candidate warning headers: {len(audit['new_owned_warning_headers'])}; inherited header regressions: {len(audit['regressions'])}.",
          f"Independent TERMINATED proof: {proofs[-1]}; VM {report['vm_id']}; stop {report['vm_last_stop']}.",
          'Exact charge retains the graph factor on both sides. Coarse exponent is 3*D*(i+j+k)+6*D*k. Carriers, partition, actual A8 summand and all original hypotheses are preserved.',
          'Repairs are compiler/statement repairs only; helper/development increments 0. Every attempt is preserved. No local Lean/Lake/elan execution; unrelated tracked dirt and untracked Lean hashes preserved.',
          'No three-lens reviews. S3132 route-final acceptance and S3137 full certification remain open.',
          'Selective Git commit/push follows only if this acceptance is green; delivery receipts are recorded separately.']
(p/'report.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')
files={str(f.relative_to(p)):file_sha(f) for f in p.rglob('*') if f.is_file() and f.name!='evidence-files.sha256.json' and '__pycache__' not in f.parts}
(p/'evidence-files.sha256.json').write_text(json.dumps(files,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'green':audit['green'],'report':str(p/'report.txt'),'evidence_files':len(files),'preserved_unrelated_files':len(before)},indent=2))
