"""Qualified-green-bound preflight and one GCP metadata trace with exact custody."""
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import sys
import tarfile
import full100_capture_gates as full100_controller
from prepare_builder02_full100 import OUTPUT
from prepare_builder02_full91 import REQUESTS as SOURCE_SIZE_REQUESTS
from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS
from prepare_builder02_full100 import REQUESTS as BRIDGE_REQUESTS
REQUESTS = SOURCE_SIZE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS
from prepare_builder02_full90 import REQUEST as ORIGINAL_MATERIAL_REQUEST
ADDITIONAL_REQUESTS = [ORIGINAL_MATERIAL_REQUEST] + REQUESTS
from full100_builder02_controller import context, local_gates, VM, VM_ID, audit_terminal
from custody_checks import digest, verify_local_custody

BASE = OUTPUT
ROOT = BASE/'consumption-v2'
STAGE = '/home/dfredriksen_quantyra_org/full100-consumption-v2-stage'
REMOTE = '/home/dfredriksen_quantyra_org/full100-consumption-v2-evidence.tar.gz'

def save(path, value):
    with Path(path).open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)

def require_qualified_green(audited, qualified, pin):
    if not audited['compile_green'] or not qualified['full_original_A22_HC46_selected_native_gates_green']:
        raise RuntimeError('Full qualified native GREEN required')
    if qualified['all_seven_stage_exits'] != [0]*7:
        raise RuntimeError('Incomplete native stage scope')
    if (qualified['original_requested_axioms'], qualified['project_closure_sources'], qualified['cache_objects_unchanged']) != (172, 327, 566):
        raise RuntimeError('Qualified verification scope differs')
    if qualified['independent_vm_status'] != 'TERMINATED':
        raise RuntimeError('Compile termination not qualified')
    if qualified['bad_profiles'] or qualified['missing_objects'] or qualified['owned_error_headers']:
        raise RuntimeError('Qualified gates are incomplete')
    if len(qualified['owned_warning_headers']) != 7 or len(qualified['inherited_regression_headers']) != 7:
        raise RuntimeError('Incomplete seven-stage warning qualification')
    if any(qualified['owned_warning_headers']) or any(qualified['inherited_regression_headers']):
        raise RuntimeError('Warning gates failed')
    if not qualified['full100_expanded_native_gates_green'] or qualified['expanded_requested_axiom_count'] != 192 or qualified['added_requested_axioms'] != ADDITIONAL_REQUESTS:
        raise RuntimeError('Expanded material native GREEN/profile scope required')
    if qualified['material_export_bad_or_missing_axioms'] or not qualified['fresh_auxiliary_inputs_preserved']:
        raise RuntimeError('Material profile or harness custody unqualified')
    if set(qualified['additional_profiles']) != set(ADDITIONAL_REQUESTS) or any(value is None or not set(value) <= {'propext','Classical.choice','Quot.sound'} for value in qualified['additional_profiles'].values()):
        raise RuntimeError('Material export nonstandard axioms')
    if qualified['custody_sha256'] != pin:
        raise RuntimeError('Qualified custody mismatch')

def ready():
    full100_controller.validate_successor()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    marker = json.loads((BASE/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    audited = audit_terminal(custody['repository_path'], marker['run'], json.loads((BASE/'capture-manifest.json').read_bytes()), loaded['common'])
    qualified_path = check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    qualified = json.loads(qualified_path.read_bytes())
    require_qualified_green(audited, qualified, custody['remote_sha256'])
    with tarfile.open(custody['repository_path']) as archive:
        native_objects = json.loads(archive.extractfile('object-after.json').read())
    if len(native_objects) != 661:
        raise RuntimeError('Complete Full100 native object inventory required')
    tooling = BASE/'consumption-preparation-v1-dag'
    readiness = json.loads((tooling/'readiness.json').read_bytes())
    if (readiness['requested_roots_exact'],readiness['focused_consumers_exact']) != (192,24) or readiness['additional_roots'] != REQUESTS:
        raise RuntimeError('Expanded material trace scope differs')
    if digest(tooling/'tooling.tar.gz') != readiness['tooling_archive_sha256']:
        raise RuntimeError('Prepared tooling drift')
    if readiness['capture_manifest_sha256'] != digest(BASE/'capture-manifest.json'):
        raise RuntimeError('Prepared tooling belongs to a different source capture')
    binding = dict(resource=BASE.name, run=marker['run'], qualified_native_green=True,
        qualified_report_sha256=digest(qualified_path), native_archive_sha256=custody['remote_sha256'],
        capture_manifest_sha256=digest(BASE/'capture-manifest.json'),
        helper_sha256=json.loads((BASE/'resource-binding.json').read_bytes())['helper_sha256'],
        original_remote_controls=marker['remote_controls'], tooling_readiness=readiness,
        worker_sha256=digest(Path(__file__).with_name('full100_consumption_v2_worker.py')),
        accepted=False, review_required=True)
    ROOT.mkdir(exist_ok=True)
    path = ROOT/'green-binding.json'
    if path.exists():
        if json.loads(path.read_bytes()) != binding:
            raise RuntimeError('Frozen trace binding drift')
    else:
        save(path, binding)
    return loaded, runner, binding

def main(execute=False):
    loaded, runner, binding = ready()
    runner.VM = VM
    check = ROOT/'checks'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    check.mkdir(parents=True)
    class TraceControl(runner.Control):
        def cloud(self, args, **kwargs):
            if args[:3] == ['compute', 'instances', 'describe']:
                if args[3] != VM: raise RuntimeError('Foreign VM')
            elif args[:2] in (['compute', 'ssh'], ['compute', 'scp']):
                if args[:2] == ['compute', 'ssh'] and args[2] != VM: raise RuntimeError('Foreign SSH target')
                if args[:2] == ['compute', 'scp'] and args[2] != VM+':'+REMOTE: raise RuntimeError('Foreign SCP source')
            else: raise RuntimeError('Only inspection and owned transport are permitted')
            return super().cloud(args, **kwargs)
    control = TraceControl(check)
    _, out, _ = control.cloud(['compute', 'instances', 'describe', VM, '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
    state = json.loads(out)
    if state['name'] != VM or str(state['id']) != VM_ID or state['zone'].rsplit('/', 1)[-1] != 'us-central1-a':
        raise RuntimeError('Unexpected GCP identity')
    if state['status'] != 'RUNNING' or state['machineType'].rsplit('/', 1)[-1] != 'e2-highmem-8':
        raise RuntimeError('Dedicated resource not ready')
    if any(nic.get('accessConfigs') for nic in state['networkInterfaces']):
        raise RuntimeError('External IP is attached')
    control.authenticated = True
    expected = {'full100_consumption_v2_worker.py': binding['worker_sha256'],
                'green-binding.json': digest(ROOT/'green-binding.json'),
                'tooling.tar.gz': binding['tooling_readiness']['tooling_archive_sha256']}
    _, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
        '--command=sha256sum '+' '.join(STAGE+'/'+name for name in expected)])
    actual = {line.split()[1].rsplit('/', 1)[-1]: line.split()[0].upper() for line in out.decode().splitlines()}
    if actual != expected: raise RuntimeError('Staged controls or tooling drift')
    _, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
        '--command=python3 -B '+STAGE+'/full100_consumption_v2_worker.py '+STAGE])
    preflight = json.loads(out)
    if not preflight['passed'] or preflight['launch_called']:
        raise RuntimeError('Read-only probe preflight failed')
    save(check/'preflight.json', dict(state=state, binding=binding, worker_preflight=preflight, execute_requested=execute))
    if not execute:
        print(json.dumps(dict(passed=True, launch_called=False, preflight=str(check))), flush=True)
        return 0
    save(ROOT/'launch-once.json', dict(run=binding['run'], preflight=str(check), staged_controls=expected,
        controller_sha256=digest(__file__)))
    snapshot = check/'executed-controls'; snapshot.mkdir()
    for name in ('full100_consumption_v2_worker.py', 'full100_consumption_v2_controller.py'):
        shutil.copyfile(Path(__file__).with_name(name), snapshot/name)
    code, _, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
        '--command=python3 -B '+STAGE+'/full100_consumption_v2_worker.py '+STAGE+' --execute'], timeout=4350, allow_failure=True)
    _, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=sha256sum '+REMOTE+'; stat -c %s '+REMOTE])
    lines = out.decode().splitlines(); pin = lines[0].split()[0].upper(); size = int(lines[1])
    short = Path('C:/a8gcp/c0fd3e11-consumption-v2.tar.gz')
    if short.exists(): raise RuntimeError('Custody path collision')
    control.cloud(['compute', 'scp', VM+':'+REMOTE, str(short), '--tunnel-through-iap'], timeout=300)
    second = check/'full100-consumption-v2-evidence.tar.gz'
    with short.open('rb') as source, second.open('xb') as destination:
        shutil.copyfileobj(source, destination)
    custody = verify_local_custody(short, second, pin, size)
    custody['vm_retained_for_other_threads'] = False
    with tarfile.open(second) as archive:
        terminal = json.loads(archive.extractfile('terminal.json').read())
        if terminal['run'] != binding['run'] or terminal['identity']['id'] != VM_ID:
            raise RuntimeError('Foreign probe evidence')
        if terminal['native_archive_sha256'] != binding['native_archive_sha256']:
            raise RuntimeError('Probe consumed different native evidence')
        if terminal['probe_sha256'] != binding['tooling_readiness']['files']['probe.lean']['sha256']:
            raise RuntimeError('Probe identity mismatch')
        raw_code = int(archive.extractfile('probe.native-exit').read())
        if raw_code != terminal['probe_native_exit']: raise RuntimeError('Probe exit mismatch')
    local_gates(loaded['common'], loaded)
    save(check/'terminal-custody.json', dict(run=binding['run'], ssh_native_exit=code, custody=custody,
        probe_terminal=terminal, native_terminal=True, coverage_accepted=False, vm_stop_performed=False))
    print(json.dumps(dict(check=str(check), probe_native_exit=raw_code, terminal=terminal)), flush=True)
    return 0 if raw_code == 0 and terminal['failure'] is None else 1

if __name__ == '__main__':
    if sys.argv[1:] == ['--prepare']:
        _, _, binding = ready(); print(json.dumps(binding, indent=2))
    elif sys.argv[1:] in ([], ['--execute']):
        raise SystemExit(main(sys.argv[1:] == ['--execute']))
    else:
        raise SystemExit('Use --prepare, read-only default, or --execute')
