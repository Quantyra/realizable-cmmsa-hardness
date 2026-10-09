"""Qualified-native-bound dedicated02 consumption staging; no probe invocation."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import shlex
import sys
from full103_consumption_v2_controller import ROOT, STAGE, VM, VM_ID, ready
from full103_builder02_controller import local_gates
from finalize_builder02_bootstrap import SDK, FLAGS
from custody_checks import digest


def main(resume=False):
    loaded, runner, binding = ready()
    local_gates(loaded['common'], loaded)
    folder = ROOT/'staging-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True)
    records = []

    def call(command):
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try: out, err = process.communicate(timeout=30); break
            except subprocess.TimeoutExpired:
                print('Same dedicated Full103 staging process remains live', process.pid, flush=True)
        number = len(records)
        (folder/f'{number}.stdout').write_bytes(out)
        (folder/f'{number}.stderr').write_bytes(err)
        records.append({'argv': command, 'native_exit': process.returncode,
                        'stdout_sha256': digest(folder/f'{number}.stdout'),
                        'stderr_sha256': digest(folder/f'{number}.stderr'),
                        'utc': datetime.now(timezone.utc).isoformat()})
        (folder/'commands.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        if process.returncode:
            raise RuntimeError('Staging command failed; preserve and inspect '+str(folder))
        return out

    def cloud(args):
        if args[:3] in (['compute','instances','describe'], ['compute','instances','start']):
            if args[3] != VM: raise RuntimeError('Foreign VM target')
        elif args[:2] in (['compute','ssh'], ['compute','scp']):
            if args[1] == 'ssh' and args[2] != VM: raise RuntimeError('Foreign SSH target')
            if args[1] == 'scp' and not args[-2].startswith(VM+':'): raise RuntimeError('Foreign SCP destination')
        else:
            raise RuntimeError('Unapproved staging operation')
        return call([SDK, *args, *FLAGS])

    def describe():
        state = json.loads(cloud(['compute','instances','describe',VM,
                                  '--format=json(name,id,status,zone,machineType,networkInterfaces)']))
        if state['name'] != VM or str(state['id']) != VM_ID or state['zone'].rsplit('/',1)[-1] != 'us-central1-a' or state['machineType'].rsplit('/',1)[-1] != 'e2-highmem-8':
            raise RuntimeError('Dedicated Full103 identity mismatch')
        if any(nic.get('accessConfigs') for nic in state['networkInterfaces']):
            raise RuntimeError('Unexpected external IP; retain original resource state')
        return state

    auth = json.loads(call([SDK,'auth','list','--filter=status:ACTIVE','--format=json(account,status)',
                           '--account=dfredriksen@quantyra.org','--project=quantyra-lean-cert-20260915','--quiet']))
    if not any(row['account'] == 'dfredriksen@quantyra.org' and row['status'] == 'ACTIVE' for row in auth):
        raise RuntimeError('Required active account absent')
    before = describe()
    if before['status'] != ('RUNNING' if resume else 'TERMINATED'):
        raise RuntimeError('Dedicated VM already running or transitioning; inspect before new start')
    if (ROOT/'launch-once.json').exists():
        raise RuntimeError('Full103 attempt already exists; retain original handle')
    if resume:
        previous = sorted(p for p in (ROOT/'staging-controls').glob('*/commands.json') if p.parent != folder)
        if not previous: raise RuntimeError('No original staging failure receipt')
        failed = previous[-1]
        prior_commands = json.loads(failed.read_bytes())
        last = prior_commands[-1]
        remote_commands = [arg for arg in last['argv'] if arg.startswith('--command=')]
        if last['native_exit'] != 1 or last['argv'][1:4] != ['compute','ssh',VM] or len(remote_commands) != 1 or not remote_commands[0].startswith('--command=python3 -c ') or STAGE not in remote_commands[0]:
            raise RuntimeError('Expected terminal transport failure absent')
        if not any(row['native_exit'] == 0 and row['argv'][1:5] == ['compute','instances','start',VM] for row in prior_commands):
            raise RuntimeError('Original dedicated start unproven; no repeat start')
    else:
        cloud(['compute','instances','start',VM])
    after = describe()
    if after['status'] != 'RUNNING': raise RuntimeError('Dedicated start not proven')
    directory_check = 'from pathlib import Path; p=Path('+repr(STAGE)+'); assert not p.exists() or not any(p.iterdir()), "Nonempty staging directory: inspect before transfer"; p.mkdir(exist_ok=True)'
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=python3 -c '+shlex.quote(directory_check)])
    paths = [str(ROOT/'green-binding.json'), str(ROOT.parent/'consumption-preparation-v1-dag/tooling.tar.gz'), str(Path(__file__).with_name('full103_consumption_v2_worker.py'))]
    cloud(['compute','scp',*paths,VM+':'+STAGE+'/', '--tunnel-through-iap'])
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    preflight = json.loads(cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=python3 -B '+STAGE+'/full103_consumption_v2_worker.py '+STAGE]))
    if not preflight['passed'] or preflight['launch_called']: raise RuntimeError('Read-only consumption preflight failed')
    final = describe()
    receipt = {'before': before, 'after': final, 'authentication': auth,
               'worker_preflight': preflight, 'compiler_invoked': False,
               'launch_clearance': False, 'other_vm_modified': False,
               'resumed_after_preserved_transport_failure': resume}
    (folder/'staged.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    local_gates(loaded['common'], loaded)
    print(json.dumps({'staging_receipt': str(folder/'staged.json'), 'prepared': True,
                      'compiler_invoked': False, 'launch_clearance': False}), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--resume-staging']): raise SystemExit('Default or --resume-staging')
    main(sys.argv[1:] == ['--resume-staging'])
