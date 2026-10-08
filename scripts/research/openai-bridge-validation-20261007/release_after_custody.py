"""GCP-only lease release after actual local custody and remote terminal checks.

The controlling workstation calls this only after verify_local_custody succeeds.
This independently rechecks the remote archive, GCP identity, owned processes
and mounts. A caller's boolean alone cannot release a lease.
"""
import json
from pathlib import Path
import runpy
import sys
from custody_checks import digest, verify_worker_terminal
from shared_worker import validate_spec, owned_processes
from thread_leases import release


def main(request):
    if sys.platform != 'linux': raise RuntimeError('GCP-only lease release')
    spec = request['spec']; validate_spec(spec)
    home = Path.home().resolve()
    if str(home) != '/home/dfredriksen_quantyra_org': raise RuntimeError('Unexpected VM user')
    work = home / spec['run']
    if json.loads((work / '.shared-run-owner.json').read_bytes()) != {'thread': spec['thread'], 'run': spec['run']}:
        raise RuntimeError('Workspace ownership changed')
    if digest(work / 'cloud_capture.py') != spec['helper_sha256'] or digest(work / 'capture-manifest.json') != spec['manifest_sha256']:
        raise RuntimeError('Immutable helper/manifest changed')
    frozen = runpy.run_path(str(work / 'cloud_capture.py'), run_name='custody_release_identity')
    frozen['require_gcp'](json.loads((work / 'capture-manifest.json').read_bytes()))
    archive = home / 'cmmsa-evidence' / (spec['run'] + '-evidence.tar.gz')
    custody = request['custody']
    expected = digest(archive)
    if any(custody[key] != expected for key in ('remote_sha256', 'short_sha256', 'repository_sha256')):
        raise RuntimeError('Remote archive differs from verified workstation custody')
    if archive.stat().st_size != custody['bytes']: raise RuntimeError('Evidence archive size differs')
    terminal = verify_worker_terminal(archive, spec)
    if owned_processes(work): raise RuntimeError('Owned native processes still active;retain lease')
    for line in Path('/proc/self/mountinfo').read_text().splitlines():
        target = Path(line.split()[4])
        if target == work or work in target.parents:
            raise RuntimeError('Owned mount still active;retain lease')
    registry = Path('/var/lib/quantyra-thread-leases')
    # Ownership validation and atomic movement occur under release's admission
    # lock. Write supplemental receipts only to the uniquely completed run,
    # never to an active path that another controller could have replaced.
    destination = release(registry, spec['thread'], spec['run'], native_terminal=terminal['native_terminal'], custody_verified=True)
    (destination / 'verified-custody-request.json').write_text(json.dumps(request, indent=2) + '\n')
    receipt = {'thread': spec['thread'], 'run': spec['run'], 'completed_lease': str(destination),
               'archive_sha256': expected, 'native_exit': terminal['native_exit'],
               'worker_compile_green': terminal['worker_compile_green'], 'owned_processes_quiescent': True,
               'owned_mounts_released': True, 'vm_stop_performed': False,
               'qualified_acceptance_and_reviews_required': True}
    (destination / 'release-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__': main(json.loads(Path(sys.argv[1]).read_bytes()))
