"""Independently verify complete exact recovery plans, receipts and journals."""
from datetime import datetime, timezone
import json
from pathlib import Path
import shlex
from custody_checks import digest
from full120_builder02_controller import ROOT, context, local_gates
from full114_dedicated_openssh_v2 import Session
from run_full120_cache_recovery_v1 import settled
from run_full120_cache_recovery_v1 import RECOVERY, DERIVATION, scopes, operation, verified_plans

HERE = Path(__file__).resolve().parent
AUDIT = RECOVERY / 'complete-audit-v1'


def validate_local_audit():
    report = json.loads((AUDIT / 'audit.json').read_bytes())
    assert report['numbers'] == [s['number'] for s in scopes()] and report['all_rows_match']
    assert report['disk_available_bytes'] >= 40 * 1024**3
    assert not report['compiler_invoked'] and not report['power_operation']
    for row in report['files']:
        path = Path(row['path'])
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    for scope in scopes():
        operation(scope['number'], 'plan'); operation(scope['number'], 'execute')
    return report


def main():
    settled(); loaded, _ = context(); local_gates(loaded['common'], loaded)
    selected = scopes(); summaries = verified_plans(); files = []
    def register(path):
        path = Path(path)
        files.append(dict(path=str(path), bytes=path.stat().st_size, sha256=digest(path)))
    for path in (Path(__file__).resolve(), DERIVATION, Path(json.loads((ROOT/'start-once.json').read_bytes())['original_start_folder'])/'0.lifecycle.json', Path(json.loads((ROOT/'start-once.json').read_bytes())['original_start_folder'])/'1.lifecycle.json'):
        register(path)
    for scope in selected:
        pp, pr = operation(scope['number'], 'plan'); ep, er = operation(scope['number'], 'execute')
        plan = json.loads(Path(pr['local_result']).read_bytes()); receipt = json.loads(Path(er['local_result']).read_bytes())
        assert receipt['applied'] == plan['rows']
        assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
        assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
        assert not any(receipt[k] for k in ('warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked'))
        assert pr['helper_sha256'] == er['helper_sha256'] == scope['helper_sha256'] == digest(HERE / scope['helper'])
        for path in (pp, ep, pr['local_result'], er['local_result'], HERE / scope['helper']):
            register(path)
    AUDIT.mkdir(exist_ok=False)
    with Session(AUDIT / 'transport') as session:
        for scope, summary in zip(selected, summaries):
            session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active')
            guest = "import hashlib,importlib.util,json\nfrom pathlib import Path\nroot=Path(" + repr(scope['remote_control']) + ")\nhelper=root/" + repr(scope['helper']) + "\nassert hashlib.sha256(helper.read_bytes()).hexdigest().upper()==" + repr(scope['helper_sha256']) + "\nspec=importlib.util.spec_from_file_location('guard',helper)\nmodule=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.guards()\nprint(json.dumps({n:hashlib.sha256((root/n).read_bytes()).hexdigest().upper() for n in ('execution-journal.jsonl','execute-once.json')}))\n"
            guest += "old,canonical=module.guards()\nplan=json.loads((root/'plan.json').read_bytes())\nfor row in plan['rows']:\n rel=Path(row['relative']);path=old/rel;target=canonical/rel\n assert path.is_symlink() and path.resolve()==target.resolve() and path.resolve().is_relative_to(canonical)\n assert path.stat().st_size==target.stat().st_size==row['bytes']\n assert module.digest(path)==module.digest(target)==row['sha256']\n"
            metadata = json.loads(session.python(guest).read_bytes()); decoded = {}
            for name in ('execution-journal.jsonl', 'execute-once.json'):
                path = session.ssh('cat ' + shlex.quote(scope['remote_control'] + '/' + name))
                assert digest(path) == metadata[name]; register(path); decoded[name] = path.read_bytes()
            _, pr = operation(scope['number'], 'plan'); plan = json.loads(Path(pr['local_result']).read_bytes())
            journal = [json.loads(line) for line in decoded['execution-journal.jsonl'].splitlines()]
            marker = json.loads(decoded['execute-once.json'])
            assert journal == plan['rows'] and marker['plan_sha256'] == summary['plan_sha256'] and not marker['compiler_invoked']
            summary['journal_rows'] = len(journal)
        final = json.loads(session.python("import json,shutil\nprint(json.dumps(dict(disk_available_bytes=shutil.disk_usage('/home/dfredriksen_quantyra_org').free)))\n").read_bytes())
        state = session.state
    assert final['disk_available_bytes'] >= 40 * 1024**3
    for path in AUDIT.rglob('*'):
        if path.is_file() and not any(r['path'] == str(path) for r in files):
            register(path)
    local_gates(loaded['common'], loaded)
    report = dict(schema='full120-selected-settled-generated-recovery-audit-v1', utc=datetime.now(timezone.utc).isoformat(),
        numbers=[s['number'] for s in selected], scopes=summaries, files=files, all_rows_match=True,
        disk_available_bytes=final['disk_available_bytes'], state=state,
        original_archive_source_terminal_and_quiescence_guards_passed=True,
        compiler_invoked=False, power_operation=False, mathematical_acceptance=False,
        generated_paths_repointed_with_identical_content=True, project_source_and_project_proof_objects_excluded=True,
        legacy_source_or_project_object_flag_means_content_not_path_type=True)
    (AUDIT / 'audit.json').open('x').write(json.dumps(report, indent=2) + '\n')
    validate_local_audit()
    print(json.dumps(dict(audit=str(AUDIT / 'audit.json'), rows=sum(s['rows'] for s in summaries), disk_available_bytes=report['disk_available_bytes'])), flush=True)


if __name__ == '__main__':
    main()
