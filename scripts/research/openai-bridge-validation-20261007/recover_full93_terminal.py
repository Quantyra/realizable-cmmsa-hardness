"""Observe the existing Full93 worker and collect terminal custody; never launch."""
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import time
from full93_builder02_controller import ROOT, VM, VM_ID, audit_terminal, context, local_gates
from custody_checks import digest, verify_local_custody
from finalize_builder02_bootstrap import SDK, FLAGS


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight']).resolve(strict=True)
    if not check.is_relative_to((ROOT / 'checks').resolve()):
        raise RuntimeError('Foreign check directory')
    if (check / 'terminal-custody.json').exists():
        raise RuntimeError('Original terminal already collected; inspect it')
    folder = check / 'recovery-controls-v1'
    folder.mkdir()
    records = []
    evidence = '/home/dfredriksen_quantyra_org/' + marker['run'] + '_evidence'
    archive = evidence + '.tar.gz'

    def call(args):
        if args[:3] in (['compute', 'instances', 'describe'], ['compute', 'instances', 'start']):
            if args[3] != VM:
                raise RuntimeError('Foreign VM target')
        elif args[:2] == ['compute', 'ssh']:
            if args[2] != VM:
                raise RuntimeError('Foreign SSH target')
        elif args[:2] == ['compute', 'scp']:
            if args[2] != VM + ':' + archive:
                raise RuntimeError('Foreign custody source')
        else:
            raise RuntimeError('Only exact dedicated VM inspection/custody-start, read-only SSH and evidence retrieval allowed')
        command = [SDK, *args, *FLAGS]
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try:
                out, err = child.communicate(timeout=30)
                break
            except subprocess.TimeoutExpired:
                print('Same recovery observation command remains live', child.pid, flush=True)
        n = len(records)
        (folder / f'{n}.stdout').write_bytes(out)
        (folder / f'{n}.stderr').write_bytes(err)
        records.append({'argv': command, 'native_exit': child.returncode,
                        'utc': datetime.now(timezone.utc).isoformat(),
                        'stdout_sha256': digest(folder / f'{n}.stdout'),
                        'stderr_sha256': digest(folder / f'{n}.stderr')})
        (folder / 'commands.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
        return child.returncode, out

    def ssh(command):
        return call(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=' + command])

    def observe_worker():
        code, out = ssh('ps -eo pid=,args=')
        if code or not out.strip():
            raise RuntimeError('Authoritative worker process observation inconclusive')
        rows = [line for line in out.decode(errors='replace').splitlines()
                if marker['run'] in line and 'full93_worker.py' in line
                and len(line.split()) > 1 and line.split()[1] == 'python3']
        if len(rows) > 1:
            raise RuntimeError('Multiple matching worker processes; inspect without relaunch')
        return rows

    code, out = call(['compute','instances','describe',VM,'--format=json(name,id,status,zone,networkInterfaces)'])
    if code: raise RuntimeError('VM identity inspection failed')
    before = json.loads(out)
    if before['name'] != VM or str(before['id']) != VM_ID or before['zone'].rsplit('/',1)[-1] != 'us-central1-a':
        raise RuntimeError('Unexpected custody VM identity')
    if any(nic.get('accessConfigs') for nic in before['networkInterfaces']): raise RuntimeError('Unexpected external IP')
    if before['status'] == 'TERMINATED':
        code, _ = call(['compute','instances','start',VM])
        if code: raise RuntimeError('Custody-only start failed; inspect original operation')
    elif before['status'] != 'RUNNING': raise RuntimeError('Observe existing transition before custody')
    (folder/'custody-start-context.json').write_text(json.dumps({'before':before,'purpose':'retrieve completed immutable Full93 evidence only','compiler_launched':False,'other_VM_modified':False},indent=2)+'\n',encoding='utf-8')

    while True:
        code, out = ssh('cat ' + evidence + '/dedicated-worker-terminal.json')
        if code == 0 and out.strip():
            try:
                terminal = json.loads(out)
            except json.JSONDecodeError:
                print('Incomplete terminal observation; recheck original worker', flush=True)
                terminal = None
            if terminal is None:
                time.sleep(5)
                continue
            if terminal['run'] != marker['run'] or terminal['host']['id'] != VM_ID or terminal['host']['name'] != VM:
                raise RuntimeError('Foreign worker terminal')
            break
        rows = observe_worker()
        if not rows:
            raise RuntimeError('Worker missing before terminal evidence; inspect without relaunch')
        print('Original Full93 worker confirmed live; terminal pending', rows[0], flush=True)
        time.sleep(15)

    # The worker writes terminal JSON before completing its tar archive.
    while True:
        if observe_worker():
            print('Original worker still finalizing archive; waiting before custody hash', flush=True)
            time.sleep(10)
            continue
        code, out = ssh('sha256sum ' + archive + '; stat -c %s ' + archive)
        if code == 0 and len(out.decode().splitlines()) == 2:
            lines = out.decode().splitlines()
            pin, size = lines[0].split()[0].upper(), int(lines[1])
            break
        print('Same terminal worker archive still pending; no new launch', flush=True)
        time.sleep(10)
    short = Path('C:/a8gcp') / (marker['run'].rsplit('_', 1)[1] + '.tar.gz')
    second = check / (marker['run'] + '_evidence.tar.gz')
    if short.exists() or second.exists():
        raise RuntimeError('Evidence destination exists; inspect partial custody before recovery')
    code, _ = call(['compute', 'scp', VM + ':' + archive, str(short), '--tunnel-through-iap'])
    if code:
        raise RuntimeError('Evidence transfer failed; retain partial bytes and receipts')
    with short.open('rb') as source, second.open('xb') as target:
        shutil.copyfileobj(source, target)
    custody = verify_local_custody(short, second, pin, size)
    loaded, _ = context()
    manifest = json.loads((ROOT / 'capture-manifest.json').read_bytes())
    native = audit_terminal(second, marker['run'], manifest, loaded['common'])
    local_gates(loaded['common'], loaded)
    receipt = {'run': marker['run'], 'custody': custody, 'terminal': native,
               'original_controller_terminal_custody_incomplete': True, 'same_attempt_evidence_recovered': True,
               'recovery_controls': str(folder), 'worker_restart_performed': False, 'custody_VM_start_context': str(folder/'custody-start-context.json'),
               'vm_stop_performed': False, 'accepted': False}
    with (check / 'terminal-custody.json').open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2)
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
