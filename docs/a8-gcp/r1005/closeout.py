"""Produce bounded closeout from retained receipts, never compile or change proofs."""
from pathlib import Path
import json, sys
from common import PACKAGE, REPO, SOURCE, CHECKS, FROZEN, file_sha, inherited_now, json_bytes, write_new

run = PACKAGE / 'runs' / sys.argv[1]
result = json.loads((run / 'prospective-audit.json').read_bytes())
terminal = json.loads((run / 'terminal.json').read_bytes())
manifest = json.loads((run / 'manifest.json.snapshot').read_bytes())
proofs = []
for folder in sorted(run.glob('independent-terminal-*')):
    receipt = json.loads((folder / 'receipt.json').read_bytes())
    state = json.loads((folder / 'stdout').read_bytes())
    if receipt.get('terminated_verified') and receipt['native_exit'] == 0:
        assert receipt['stdout_sha256'] == file_sha(folder / 'stdout')
        assert state['id'] == terminal['vm_terminal_receipt']['id']
        proofs.append(folder.relative_to(PACKAGE).as_posix())
assert proofs, 'Independent termination proof required'
exits = {name: int((run / 'remote-evidence' / name).read_text()) for name in ['native-exit', 'aggregate.native-exit', 'finish.native-exit']}
before = json.loads((PACKAGE / 'captures' / manifest['capture'] / 'inherited-files-before.json').read_bytes())
assert inherited_now() == before, 'Inherited file drift'
assert file_sha(REPO / SOURCE) == result['source_sha256']
assert file_sha(REPO / CHECKS) == result['checks_sha256']
report = dict(result)
report.update({'bounded_acceptance_green': result['green'], 'compiler_attempt_status': 'GREEN' if result['green'] else 'RED',
    'bounded_increment_status': 'ACCEPTED: existing S3132/A8 compiler retry' if result['green'] else 'NOT ACCEPTED',
    'owning_story_status': 'S3132 PARTIAL; no story completion', 'full_manuscript_certification_status': 'INCOMPLETE',
    'initial_source_sha256': FROZEN[SOURCE], 'initial_checks_sha256': FROZEN[CHECKS],
    'compiler_attempts': len(list((PACKAGE / 'runs').glob('*/terminal.json'))),
    'helper_development_increments_from_compiler_repairs': 0,
    'remote_exits': exits, 'independent_terminal_proofs': proofs,
    'vm': terminal['vm_terminal_receipt'], 'project': manifest['resource_plan']['project'],
    'zone': manifest['resource_plan']['zone'], 'run_started_utc': json.loads((run / 'request.json').read_bytes())['started_utc'],
    'run_finished_utc': terminal['finished_utc'], 'manifest_sha256': file_sha(run / 'manifest.json.snapshot'),
    'input_archive_sha256': manifest['files']['input-archive.tar.gz']['sha256'],
    'cloud_evidence_archive_sha256': terminal['evidence_archive_sha256'],
    'local_compilation': False, 'unrelated_dirty_files_preserved': True,
    'route_assessment': 'Directly derivable using general carrier coordinate transport and actual W6 specialization',
    'reviews': {'proof_adversarial':'INCOMPLETE', 'complexity':'INCOMPLETE', 'non_claims':'INCOMPLETE'},
    'git_status': 'Pending green-only selective delivery' if result['green'] else 'NO COMMIT OR PUSH: user green-only delivery rule',
    'warning_comparison_scope': 'Executed stages only; skipped stages have no diagnostics',
    'statement_preservation_stop': not result['green'],
    'axiom_output_status': 'All four profiles available' if result.get('axiom_profiles') else 'UNAVAILABLE: source failed; Checks and fresh-axiom stages skipped'})
write_new(PACKAGE / 'report.json', json_bytes(report))
raw_axioms = (run / 'remote-evidence/stage-3.stdout').read_text(encoding='utf-8')
axiom_lines = []
lines = raw_axioms.splitlines()
for i,line in enumerate(lines):
    if 'depends on axioms:' in line or 'does not depend on any axioms' in line:
        axiom_lines.append(line)
        if 'depends on axioms:' in line and ']' not in line:
            for following in lines[i+1:]:
                axiom_lines.append(following)
                if ']' in following: break
write_new(PACKAGE / 'axioms-exact.txt', ('\n'.join(axiom_lines)+'\n' if axiom_lines else 'UNAVAILABLE for all four exports: source stage failed; Checks and fresh-axiom stages skipped. Raw stage-3 stdout is empty. No acceptable axiom envelope is certified.\n').encode('utf-8'))
text = f'''# S3132 bounded A8 output-coordinate compiler receipt

- Compiler-attempt status: {report['compiler_attempt_status']} ({report['compiler_attempts']} attempt(s)).
- Bounded-increment status: {report['bounded_increment_status']}.
- Owning-story status: S3132 PARTIAL.
- Full-manuscript certification: INCOMPLETE; S3137 warning-policy debt and route-final review debt remain.

Run: `{run.name}`. No local Lean, Lake, or elan execution. Route assessment: {report['route_assessment']}.

Initial source SHA256: `{FROZEN[SOURCE]}`
Final source SHA256: `{result['source_sha256']}`
Initial Checks SHA256: `{FROZEN[CHECKS]}`
Final Checks SHA256: `{result['checks_sha256']}`
Manifest SHA256: `{report['manifest_sha256']}`
Input archive SHA256: `{report['input_archive_sha256']}`
Cloud evidence archive SHA256: `{report['cloud_evidence_archive_sha256']}`

| Stage | Exit | Legacy warning-text count | Errors | Unsolved goals | Actual warning headers |
|---|---:|---:|---:|---:|---:|
'''
for row,warning in zip(result['compiler_stage_results'],result['warning_stage_results']):
    text += f"| {row['name']} | {row['native_exit']} | {row['warnings']} | {row['errors']} | {row['unsolved_goals']} | {warning['total_warning_headers']} |\n"
text += f'''
Warning policy: zero new owned headers ({sum(result['new_owned_warning_headers'].values())}); no inherited header regressions ({sum(result['regressions'].values())}) in the executed stages against the pre-launch frozen accepted A9 logs and exact dependency/configuration identities. Skipped stages have no diagnostics and supply no success evidence. Frozen union: {result['frozen_baseline_header_union']} headers. Legacy zero-total-warning audit GREEN: {result['legacy_zero_total_audit_green']}; retained unchanged. Warning-text counts can include multiline hints and repeated replay across stages. Inherited warnings remain S3137 debt, not mathematical critical-path work. No suppression introduced.

Exact `#print axioms` output for all four exports:

```text
{chr(10).join(axiom_lines) if axiom_lines else report['axiom_output_status'] + '. Raw stage-3 stdout is empty. No axiom envelope is certified.'}
```

VM `{report['vm']['name']}`, id `{report['vm']['id']}`, project `{report['project']}`, zone `{report['zone']}` independently confirmed TERMINATED. Start: `{report['vm'].get('lastStartTimestamp')}`; stop: `{report['vm'].get('lastStopTimestamp')}`. Controller window: `{report['run_started_utc']}` to `{report['run_finished_utc']}`. Independent receipts: {', '.join(proofs)}.

All immutable inputs, exact dependency/configuration hashes, compiler identity, raw stdout/stderr, command/exit receipts, source/object inventories, failed attempts (if any), and finally-style cleanup receipts are retained under this directory. Unrelated dirty worktree file hashes are unchanged. Compiler repairs count as attempts and zero helper/development increments; approved statements and assumptions remain the boundary.

| Review lens | Status |
|---|---|
| Build/axiom/warning audit | {'GREEN' if result['green'] else 'RED'} |
| Proof-adversarial | INCOMPLETE |
| Complexity | INCOMPLETE |
| Non-claims | INCOMPLETE |

These route-final lenses and final provider reviews are not claimed complete. This receipt accepts at most one bounded analytic A8 increment, without owning-story or manuscript completion.

Git: {report['git_status']}. This is the single authorized compiler retry for existing S3132/A8. Luna supplied the exact transpose orientation correction. Sol made no source repair. Claims and assumptions were unchanged. No successor increment was launched. Exact compiler diagnostics are retained in owned-diagnostics.txt and the raw stage logs.
'''
write_new(PACKAGE / 'report.txt', text.encode('utf-8'))
print(json.dumps({'green': result['green'], 'report': str(PACKAGE / 'report.txt'), 'independent_terminal_proofs': proofs}, indent=2))
