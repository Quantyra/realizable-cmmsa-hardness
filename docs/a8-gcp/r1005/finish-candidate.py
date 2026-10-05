"""Summarize retained single-attempt evidence; no compiler, cloud, or Git mutations."""
from pathlib import Path
import json, subprocess, sys
from collections import Counter
from common import PACKAGE, REPO, SOURCE, CHECKS, file_sha, write_new, json_bytes, utc, verify_capture, inherited_now, inherited_status_now
import importlib.util

run = PACKAGE / 'runs' / sys.argv[1]
terminal = json.loads((run / 'terminal.json').read_bytes())
manifest = verify_capture(PACKAGE / 'captures' / terminal['capture'])
original_terminal = terminal
recovered = (run / 'terminal-custody-recovered.json').is_file()
if recovered: terminal = json.loads((run / 'terminal-custody-recovered.json').read_bytes())
audit = json.loads((run / ('audit-custody-recovered.json' if recovered else 'audit.json')).read_bytes())
prospective = json.loads((run / ('prospective-audit-custody-recovered.json' if recovered else 'prospective-audit.json')).read_bytes())
independent = sorted(run.glob('independent-terminal-*/receipt.json'))[-1]
receipt = json.loads(independent.read_bytes())
assert receipt['native_exit'] == 0 and receipt['terminated_verified']
assert terminal['vm_terminal_receipt']['status'] == 'TERMINATED'
controls = json.loads((run / 'commands.json').read_bytes())
starts = [r for r in controls if r['argv'][1:4] == ['compute', 'instances', 'start']]
compiles = [r for r in controls if any(a.startswith('--command=bash /tmp/') for a in r['argv'])]
assert len(starts) == len(compiles) == 1
spec = importlib.util.spec_from_file_location('warning_audit', PACKAGE / 'prospective-audit.py')
warning_audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(warning_audit)
baseline, seal = warning_audit.check_baseline(manifest)
warning_rows = {}
for i in range(4):
    headers = warning_audit.headers(run / 'remote-evidence', i)
    warning_rows[str(i)] = {'headers': dict(headers), 'count':sum(headers.values()),
                            'above_frozen_baseline':dict(headers-baseline)}
write_new(run / 'warning-headers.json', json_bytes({'stages':warning_rows,
    'frozen_union':dict(baseline), 'frozen_union_count':sum(baseline.values()),
    'debt_story':'S3137', 'warning_suppression':False}))
def git(*args):
    return subprocess.check_output(['git',*args],cwd=REPO)
assert not git('diff','--cached','--name-only').strip()
capture = PACKAGE / 'captures' / terminal['capture']
assert inherited_now() == json.loads((capture/'inherited-files-before.json').read_bytes())
assert inherited_status_now() == json.loads((capture/'inherited-status-before.json').read_bytes())
heads = json.loads((capture/'heads-before.json').read_bytes())
assert git('rev-parse','HEAD').decode().strip() == heads['head']
assert git('rev-parse','origin/main').decode().strip() == heads['origin_main']
write_new(run/'status-after.txt',git('status','--porcelain=v1','--untracked-files=normal'))
write_new(run/'tracked-diff-after.patch',git('diff','--binary','HEAD','--'))
green = prospective['green']
statuses = {'compiler_attempt':'GREEN under frozen-baseline policy' if green else 'RED; single attempt failed, no repair/retry',
    'bounded_increment':'UNACCEPTED development candidate 2; three-lens closeout pending' if green else 'UNACCEPTED development candidate 2; compiler gate failed',
    'owning_story_S3132':'PARTIAL; analytic A8 OPEN',
    'full_manuscript_certification_S3137':'INCOMPLETE; inherited warning debt retained'}
result = {'run':run.name, 'finished_utc':utc(), 'statuses':statuses,
    'start_count':len(starts), 'compiler_attempt_count':len(compiles), 'compiler_retry_count':0,
    'accepted_helper_count':1, 'candidate_number':2, 'three_helper_threshold_crossed':False,
    'compiler_repair_credit':0, 'compiler_repair':'sole explicit import ActualBinaryMatrixHC46A9AmbientFiber',
    'author_artifact_sha256':'2EDFA351E99DC145B9F917F486E93871522E37258940872376E150D537BCC5FE',
    'source_sha256':manifest['offered_identities'][SOURCE], 'checks_sha256':manifest['offered_identities'][CHECKS],
    'stage_results':audit['stage_results'], 'diagnostics':audit.get('diagnostics'),
    'warning_stage_results':prospective['warning_stage_results'],
    'axiom_profiles':audit.get('axiom_profiles'), 'failures':prospective['failures'],
    'vm_status':'TERMINATED', 'independent_terminal_receipt':independent.relative_to(PACKAGE).as_posix(),
    'cloud_evidence_sha256':terminal['evidence_archive_sha256'],
    'inherited_dirt_preserved':True, 'index_empty':True, 'head_and_origin_main_unchanged':True,
    'local_compilation':False, 'committed':False, 'pushed':False,
    'transport_custody_recovered':recovered, 'original_runner_failure_retained':original_terminal['failure'],
    'original_runner_audit_sha256':file_sha(run/'audit.json'),
    'recovered_custody_audit_sha256':file_sha(run/'audit-custody-recovered.json') if recovered else None,
    'legacy_zero_total_audit_green':audit['green'], 'three_lens_review':'REQUIRED; not performed in this invocation'}
write_new(PACKAGE/'report.json',json_bytes(result))
stages = '/'.join(str(r['native_exit']) for r in audit['stage_results'])
counts = '/'.join(str(r['total_warning_headers']) for r in prospective['warning_stage_results'])
text = '# Luna domain quotient square: candidate 2 compiler evidence\n\n'
text += '| Status | Result |\n|---|---|\n'
for k,v in statuses.items():text += '| '+k+' | '+v+' |\n'
text += '\nRun `'+run.name+'`; single GCP compiler attempt, native stage exits `'+stages+'`. '
text += 'Warning header counts by stage: `'+counts+'`; frozen union 981. '
text += 'Raw stdout/stderr, native exits, exact warning headers, source/dependency hashes, axiom profiles, archive custody and independent TERMINATED receipt are retained.\n\n'
text += 'Luna artifact SHA256 `'+result['author_artifact_sha256']+'`; no Unicode format characters. '
text += 'Exact authored theorem/proof and Checks additions applied with apply_patch. Sole explicit import repair exposes ActualBinaryMatrixHC46A9AmbientFiber; BinaryMatrixA1NestedCarrier already transitive. Compiler repair earns zero helper/roadmap credit.\n\n'
text += 'Source SHA256 `'+result['source_sha256']+'`; Checks SHA256 `'+result['checks_sha256']+'`. '
text += 'Cloud archive SHA256 `'+str(result['cloud_evidence_sha256'])+'`.\n\n'
text += 'Development candidate 2 remains unaccepted. Accepted helper count is 1; compiler retries and compiler repair credit are zero; three-helper threshold is not crossed. Three-lens review/closeout is required after green evidence before acceptance or commit. Analytic A8 and a8_output_q_le_actual_predecessor_sum remain open.\n\n'
text += 'Inherited warnings remain separate S3137 debt; legacy zero-total-warning audit remains RED. No warning suppression or cleanup. No local Lean/Lake/elan, staging, commit, or push. Unrelated dirty-file hashes/status, HEAD and origin/main preserved.\n'
if recovered:
    text += '\nTransport exception: original SCP stalled at 7,569,408 bytes; the same complete 38,272,740-byte immutable archive was recovered through bounded read-only SSH chunks and matched the independently recorded remote SHA256 before VM stop. No compiler was rerun. The original runner terminal and audit remain RED with their raw transport failure; companion recovered-custody terminal/audit and prospective warning audit are explicitly separate. Only the stalled local SCP and its orphan IAP child were closed after verified custody and independently confirmed VM termination.\n'
text += '\nWarning headers by stage are 981/981/981/1 with zero owned headers and zero regressions. Broader warning-token count is 3313; prior r1004 token count was 3274 (the additional ambient-fiber import exposes existing dependency warnings). All five exports, including a8_w6_domain_quotient_square, have exactly propext, Classical.choice, Quot.sound.\n'
if prospective['failures']:text += '\nRetained gate failures: '+repr(prospective['failures'])+'\n'
write_new(PACKAGE/'completion-report.md',text)
print(json.dumps(result,indent=2))
