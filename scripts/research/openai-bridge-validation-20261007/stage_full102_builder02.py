"""Authorized dedicated02 start/transport/preflight; no compiler invocation."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
from full102_capture_gates import validate_successor
from full102_builder02_controller import ROOT, STAGE, VM, VM_ID, NAMES, context, local_gates
from finalize_builder02_bootstrap import SDK, FLAGS
from custody_checks import digest


def main(resume=False):
    validate_successor()
    loaded, runner = context()
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
                print('Same dedicated Full90 staging process remains live', process.pid, flush=True)
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
            raise RuntimeError('Dedicated Full90 identity mismatch')
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
        raise RuntimeError('Full90 attempt already exists; retain original handle')
    if resume:
        prior_paths = sorted(p for p in (ROOT/'staging-controls').glob('*/commands.json') if p.parent != folder)
        if not prior_paths: raise RuntimeError('No preserved prior staging attempt')
        prior = prior_paths[-1]
        previous = json.loads(prior.read_bytes())
        if previous[-1]['native_exit'] != 1 or previous[-1]['argv'][1:4] != ['compute','ssh',VM]:
            raise RuntimeError('Original staging failure identity changed')
        if not any(r['argv'][1:5] == ['compute','instances','start',VM] and r['native_exit'] == 0 for r in previous):
            raise RuntimeError('Original dedicated start unproven')
        cloud(['compute','ssh',VM,'--tunnel-through-iap',
               '--command=set -e; test ! -e '+STAGE+'; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json'])
    else:
        cloud(['compute','instances','start',VM])
    after = describe()
    if after['status'] != 'RUNNING': raise RuntimeError('Dedicated start not proven')
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=mkdir '+STAGE])
    paths = [str(ROOT/name) for name in ['input-archive.tar.gz','capture-manifest.json','resource-binding.json']]
    paths += [str(Path(__file__).with_name(name)) for name in NAMES]
    cloud(['compute','scp',*paths,VM+':'+STAGE+'/', '--tunnel-through-iap'])
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=python3 -B '+STAGE+'/full102_verify.py '+STAGE+' full102-spectral-owned-warning-repair-resource02'])
    preflight = json.loads(cloud(['compute','ssh',VM,'--tunnel-through-iap',
                                 '--command=cat '+STAGE+'/dependency-preflight.json']))
    final = describe()
    receipt = {'before': before, 'after': final, 'authentication': auth,
               'dependency_preflight': preflight, 'compiler_invoked': False,
               'launch_clearance': False, 'other_vm_modified': False}
    (folder/'staged.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    local_gates(loaded['common'], loaded)
    print(json.dumps({'staging_receipt': str(folder/'staged.json'), 'prepared': True,
                      'compiler_invoked': False, 'launch_clearance': False}), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--resume-staging']):
        raise SystemExit('Default staging or --resume-staging required')
    main(sys.argv[1:] == ['--resume-staging'])
