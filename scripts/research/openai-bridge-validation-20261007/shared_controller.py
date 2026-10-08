"""Full83 local GCP controller. Default is read-only preflight, not launch.

Retains the original capture and approved preservation context. Never starts,
stops, deletes or resizes a VM. One --execute attempt owns one persistent local
marker through native terminal, exact custody and owned remote lease release.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
from custody_checks import digest, verify_local_custody, verify_worker_terminal
from shared_worker import validate_spec

BASE = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81')
PACKET = Path('C:/Users/dfred/.quantyra/shared-runtime-packets/cmmsa_a8_output_20261008T020037Z_fc1d0cd7')
ADAPTER_SHA = 'c02f00c8527dd4474884b2e7948cc4aed0fec6fcc3a4a81d633abceb11e57f11'
MANIFEST_SHA = 'AEB36ED4DA0D9CED89A0B3D070F7B2ED40D70A7D06CA1589115C526EB981BE5C'
HEAD = '7fc1ec119880be28fe21714ff7e6e681e7dfe4b2'
ORIGIN = '8c3d3f741a1435d671df6325e14e66338a1c22dd'


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream: stream.write((json.dumps(value, indent=2) + '\n').encode())


def context():
    adapter = BASE / 'resume-with-approved-archive-preservation.py'
    assert hashlib.sha256(adapter.read_bytes()).hexdigest() == ADAPTER_SHA
    text = adapter.read_text().split("if sys.argv[1:]==['--verify-only']:")[0]
    text = text.replace("package/'retry-81/controller.py'", "package/'retry-83/controller.py'")
    previous = sys.argv
    sys.argv = [str(adapter), '--verify-only']
    try:
        namespace = {'__file__': str(adapter), '__name__': 'shared_approved_preservation'}
        exec(compile(text, str(adapter), 'exec'), namespace)
        loaded = runpy.run_path(str(namespace['package'] / 'retry-83/controller.py'), run_name='shared_full83')
        runner = loaded['configure']()
        return loaded, runner
    finally: sys.argv = previous


def heads(repo):
    return {key: subprocess.check_output(['git', '-C', str(repo), 'rev-parse', ref]).decode().strip()
            for key, ref in [('head', 'HEAD'), ('origin_main', 'origin/main')]}


def cloud_operation_allowed(args):
    if args[:3] == ['compute', 'instances', 'describe']: return True
    if args[:2] in (['compute', 'ssh'], ['compute', 'scp']): return True
    raise ValueError('Shared controller prohibits VM lifecycle/resource mutation')


def admission_ready(readiness, spec, manager_verified):
    if not isinstance(readiness, dict) or manager_verified is not True: return False
    enrolled = readiness.get('enrolled_threads')
    return (readiness.get('ready') is True and readiness.get('vm_id') == '8337954477286097405'
            and readiness.get('controller_inventory_complete') is True
            and readiness.get('all_controllers_lease_aware') is True
            and isinstance(enrolled, list) and spec['thread'] in enrolled)


def main(execute=False):
    report = json.loads((PACKET / 'packet-report.json').read_bytes())
    for name, expected in report['files'].items():
        if digest(PACKET / name) != expected: raise RuntimeError('Prepared packet drift: ' + name)
    spec = json.loads((PACKET / 'spec.json').read_bytes()); validate_spec(spec)
    loaded, runner = context(); common = loaded['common']; repo = common.REPO
    runner.DESCRIBE = ['compute', 'instances', 'describe', runner.VM,
                      '--format=json(name,id,status,zone,machineType,lastStartTimestamp,lastStopTimestamp)']
    capture = common.PACKAGE / 'captures/capture-full-a22-hc46-83'
    if digest(capture / 'manifest.json') != MANIFEST_SHA: raise RuntimeError('Frozen capture drift')
    manifest = common.verify_capture(capture, live=False)
    inner = json.loads((capture / 'inputs/capture-manifest.json').read_bytes())
    expected_warm = {rel.removeprefix('.lake/'): value for rel, value in inner['cache_provenance']['objects'].items()}
    if (spec['thread'] != 'cmmsa_full83' or spec['run'] != PACKET.name
            or report['frozen_manifest_sha256'] != MANIFEST_SHA
            or spec['helper_sha256'] != manifest['files']['inputs/cloud_capture.py']['sha256']
            or spec['manifest_sha256'] != manifest['files']['inputs/capture-manifest.json']['sha256']
            or spec['warm_run'] != inner['cache_provenance']['run'] or spec['warm_hashes'] != expected_warm
            or digest(PACKET / 'input-archive.tar.gz') != manifest['files']['input-archive.tar.gz']['sha256']):
        raise RuntimeError('Shared packet is not bound to the exact frozen Full83 capture')
    if heads(repo) != {'head': HEAD, 'origin_main': ORIGIN}: raise RuntimeError('Frozen Git context drift')
    inherited = json.loads((capture / 'inherited-files-before.json').read_bytes())
    status = json.loads((capture / 'inherited-status-before.json').read_bytes())
    if common.inherited_now() != inherited or common.inherited_status_now() != status:
        raise RuntimeError('Approved preservation context drift')
    for rel, expected in json.loads((loaded['HERE'] / 'current-dependency-pins.json').read_bytes()).items():
        if digest(repo / rel) != expected: raise RuntimeError('Live dependency drift: ' + rel)
    # All local compiler commands are excluded by the cloud argument allowlist.
    # Other research threads' local processes do not establish ownership here.
    free = shutil.disk_usage(repo).free
    required = 1024**3 + max(512 * 1024**2, 4 * Path('C:/a8gcp/6af6dc24.tar.gz').stat().st_size)
    if free < required: raise RuntimeError('Insufficient local custody reserve')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    check = Path('C:/Users/dfred/.quantyra/shared-control-checks') / stamp
    check.mkdir(parents=True)

    class SharedControl(runner.Control):
        def cloud(self, args, **kwargs):
            cloud_operation_allowed(args)
            return super().cloud(args, **kwargs)

        def settle(self):
            raise RuntimeError('Per-thread controller may not settle the shared VM')

    control = SharedControl(check)
    state = control.describe()
    readiness = {}; manager_verified = False
    if state['status'] == 'RUNNING':
        control.authenticated = True
        _, data, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                                   '--command=cat /var/lib/quantyra-thread-leases/runtime-readiness.json'], allow_failure=True)
        try: readiness = json.loads(data)
        except (ValueError, UnicodeError): readiness = {}
        if isinstance(readiness, dict) and readiness.get('ready') is True:
            _, service, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                                          '--command=systemctl show --value --property=ExecStart quantyra-idle-shutdown.service'])
            manager_names = ['shared_idle.py', 'lifecycle_manager.py', 'thread_leases.py']
            _, manager, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                '--command=sha256sum ' + ' '.join('/usr/local/lib/quantyra-shared-runtime/' + name for name in manager_names)])
            hashes = {line.split()[1].rsplit('/', 1)[1]: line.split()[0].upper() for line in manager.decode().splitlines()}
            manager_verified = (b'/usr/local/lib/quantyra-shared-runtime/shared_idle.py' in service
                                and hashes == {name: report['files'][name] for name in manager_names})
    admitted = admission_ready(readiness, spec, manager_verified)
    preflight = {'run': spec['run'], 'frozen_capture_verified': True, 'approved_preservation_verified': True,
                 'local_free_bytes': free, 'local_required_bytes': required, 'vm': state,
                 'runtime_readiness': readiness, 'effective_manager_verified': manager_verified,
                 'shared_admission_verified': admitted,
                 'full83_launched': False, 'vm_power_operations': False,
                 'local_process_scope': 'This controller executes gcloud only;per-thread lease owns the remote compiler',
                 'legacy_exclusive_resource_guard_claimed_passed': False}
    save(check / 'preflight.json', preflight)
    print(json.dumps(preflight, indent=2), flush=True)
    if not execute: return 0
    if state['status'] != 'RUNNING' or not admitted:
        raise RuntimeError('Shared VM/runtime/controller enrollment incomplete;no compiler launch or automatic start/restart')

    # The persistent marker is never removed on exception or observation timeout.
    # Resume observation/custody on this run;never execute another compiler.
    owner = Path('C:/Users/dfred/.quantyra/shared-controls') / spec['thread']
    owner.mkdir(parents=True, exist_ok=False)
    run = common.PACKAGE / 'runs' / spec['run']; run.mkdir(parents=True, exist_ok=False)
    control = SharedControl(run); control.authenticated = True
    stage = '/home/dfredriksen_quantyra_org/cmmsa-runtime-stage-' + spec['run'].rsplit('_', 1)[1]
    names = list(report['files'])
    _, data, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                               '--command=sha256sum ' + ' '.join(stage + '/' + name for name in names)])
    remote_hashes = {line.split()[1].rsplit('/', 1)[1]: line.split()[0].upper() for line in data.decode().splitlines()}
    if remote_hashes != report['files']: raise RuntimeError('Staged packet identity drift')
    short = Path('C:/a8gcp') / (spec['run'].rsplit('_', 1)[1] + '.tar.gz')
    if short.exists(): raise RuntimeError('Custody destination already exists;inspect existing run')
    save(owner / 'launch-once.json', {'run': spec['run'], 'capture_sha256': MANIFEST_SHA,
                                   'controller_sha256': digest(__file__), 'preflight': str(check)})
    save(run / 'request.json', {'spec': spec, 'controller_sha256': digest(__file__), 'capture_sha256': MANIFEST_SHA})
    executed = run / 'executed-controls'; executed.mkdir()
    for name in ('shared_controller.py', 'custody_checks.py', 'release_after_custody.py'):
        with (executed / name).open('xb') as destination:
            destination.write(Path(__file__).with_name(name).read_bytes())
    save(run / 'executed-control-hashes.json', {path.name: digest(path) for path in executed.iterdir()})
    save(run / 'launch-once.json', {'run': spec['run'], 'shared_mode': True})
    code, _, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                                '--command=python3 -B ' + stage + '/shared_worker.py ' + stage + '/spec.json'],
                               timeout=4350, allow_failure=True)
    # A nonzero SSH result is not permission to restart. Inspect actual remote
    # terminal/custody evidence;an absent archive leaves the lease/marker intact.
    remote = '/home/dfredriksen_quantyra_org/cmmsa-evidence/' + spec['run'] + '-evidence.tar.gz'
    _, data, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                               '--command=sha256sum ' + remote + '; stat -c %s ' + remote])
    lines = data.decode().splitlines(); sha = lines[0].split()[0].upper(); size = int(lines[1])
    control.cloud(['compute', 'scp', runner.VM + ':' + remote, str(short), '--tunnel-through-iap'], timeout=300)
    repository = run / (spec['run'] + '-evidence.tar.gz')
    with short.open('rb') as source, repository.open('xb') as destination: shutil.copyfileobj(source, destination)
    custody = verify_local_custody(short, repository, sha, size)
    terminal = verify_worker_terminal(repository, spec)
    save(run / 'custody.json', custody)
    if heads(repo) != {'head': HEAD, 'origin_main': ORIGIN} or common.inherited_now() != inherited or common.inherited_status_now() != status:
        raise RuntimeError('Post-run frozen context/preservation drift;retain all native evidence')
    release_request = run / 'release-request.json'; save(release_request, {'spec': spec, 'custody': custody})
    sources = [str(executed / name) for name in ('custody_checks.py', 'release_after_custody.py')]
    control.cloud(['compute', 'scp', *sources, str(release_request), runner.VM + ':' + stage + '/', '--tunnel-through-iap'])
    expected = {Path(path).name: digest(path) for path in [*sources, str(release_request)]}
    _, data, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                               '--command=sha256sum ' + ' '.join(stage + '/' + name for name in expected)])
    if {line.split()[1].rsplit('/', 1)[1]: line.split()[0].upper() for line in data.decode().splitlines()} != expected:
        raise RuntimeError('Release controls transfer identity drift')
    _, data, _ = control.cloud(['compute', 'ssh', runner.VM, '--tunnel-through-iap',
                               '--command=python3 -B ' + stage + '/release_after_custody.py ' + stage + '/release-request.json'])
    release_receipt = json.loads(data); save(run / 'owned-lease-release.json', release_receipt)
    if release_receipt['thread'] != spec['thread'] or release_receipt['run'] != spec['run'] or release_receipt['archive_sha256'] != sha:
        raise RuntimeError('Owned release receipt mismatch')
    retained_vm = control.describe()
    save(run / 'shared-terminal.json', {'run': spec['run'], 'worker_terminal': terminal,
                                      'ssh_native_exit': code, 'custody': custody,
                                      'owned_release': release_receipt, 'retained_vm': retained_vm,
                                      'qualified_acceptance_pending': True, 'vm_stop_performed': False})
    save(owner / 'terminal-custody.json', {'run': spec['run'], 'native_terminal': True, 'custody_verified': True})
    local_root = Path('C:/Users/dfred/.quantyra/shared-controls').resolve()
    completed = local_root / 'completed'
    target = completed / spec['run']
    if owner.resolve().parent != local_root or not target.resolve().is_relative_to(local_root):
        raise RuntimeError('Local completion target escapes the owned control root')
    completed.mkdir(exist_ok=True)
    if target.exists(): raise RuntimeError('Preserved local completion already exists')
    if json.loads((owner / 'launch-once.json').read_bytes())['run'] != spec['run']:
        raise RuntimeError('Local controller ownership changed')
    owner.rename(target)  # Preserve the terminal marker;admit a later successor, never rerun this run.
    print(json.dumps({'run': spec['run'], 'native_and_custody_complete': True, 'worker_terminal': terminal,
                      'qualified_acceptance_pending': True}), flush=True)
    return 0 if terminal['worker_compile_green'] else 1


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--execute']): raise SystemExit('Use default read-only preflight or --execute')
    raise SystemExit(main(execute=sys.argv[1:] == ['--execute']))
