import hashlib
import json
import pathlib
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / ('recovery-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()))
OUT.mkdir(parents=True)
GCLOUD = r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd'
VM = 'quantyra-lean-builder-01'
FLAGS = ['--project=quantyra-lean-cert-20260915', '--zone=us-central1-a']
records = []

def call(args, timeout=180, required=True):
    p = subprocess.run([GCLOUD] + args + FLAGS, capture_output=True,
                       timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
    i = len(records)
    (OUT / (str(i) + '.stdout')).write_bytes(p.stdout)
    (OUT / (str(i) + '.stderr')).write_bytes(p.stderr)
    records.append({'args': args, 'native_exit_code': p.returncode,
                    'stdout_sha256': hashlib.sha256(p.stdout).hexdigest(),
                    'stderr_sha256': hashlib.sha256(p.stderr).hexdigest()})
    (OUT / 'commands.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    if required and p.returncode:
        raise RuntimeError('Command failed; see durable record ' + str(i))
    return p.stdout

try:
    assert call(['compute', 'instances', 'describe', VM, '--format=value(status)']).strip() == b'TERMINATED'
    call(['compute', 'instances', 'start', VM, '--quiet'], timeout=300)
    command = (
        'systemctl is-active --quiet quantyra-idle-shutdown.timer && '
        'sudo systemd-run --unit=cmmsa-data-recovery-' + str(int(time.time())) +
        ' --on-active=12min /sbin/shutdown -h now && '
        'tar -czf /tmp/cmmsa-062303-recovery.tar.gz '
        '-C /tmp cmmsa_analytic_20260930T062303Z.sh '
        'cmmsa_analytic_20260930T062303Z.tar.gz '
        'cmmsa_analytic_20260930T062303Z-evidence.tar.gz '
        'cmmsa_cslib_d9be641_cache.tar.gz && '
        'sha256sum /tmp/cmmsa-062303-recovery.tar.gz')
    call(['compute', 'ssh', VM, '--quiet', '--tunnel-through-iap', '--command=' + command], timeout=420)
    call(['compute', 'scp', VM + ':/tmp/cmmsa-062303-recovery.tar.gz',
          str(OUT / 'cmmsa-062303-recovery.tar.gz'), '--quiet', '--tunnel-through-iap'], timeout=300)
    p = OUT / 'cmmsa-062303-recovery.tar.gz'
    (OUT / 'recovered.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest() + '\n', encoding='ascii')
finally:
    call(['compute', 'instances', 'stop', VM, '--quiet'], timeout=300, required=False)
    state = call(['compute', 'instances', 'describe', VM, '--format=value(status)'], required=False)
    print(json.dumps({'directory': str(OUT), 'final_vm_state': state.decode().strip()}))
