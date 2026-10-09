"""Stop dedicated builder-02 after exact probe custody and process quiescence."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import tarfile
import time
from full103_consumption_v2_controller import ROOT, ready, VM, VM_ID
from custody_checks import verify_local_custody
from finalize_builder02_bootstrap import SDK, FLAGS

def main():
    ready()
    marker = json.loads((ROOT/'launch-once.json').read_bytes())
    check = Path(marker['preflight']).resolve(strict=True)
    if not check.is_relative_to((ROOT/'checks').resolve()):
        raise RuntimeError('Foreign probe check directory')
    receipt = json.loads((check/'terminal-custody.json').read_bytes())
    if receipt['run'] != marker['run'] or not receipt['native_terminal']:
        raise RuntimeError('Probe terminal is not proven')
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    with tarfile.open(custody['repository_path']) as archive:
        terminal = json.loads(archive.extractfile('terminal.json').read())
        if terminal != receipt['probe_terminal'] or terminal['identity']['id'] != VM_ID:
            raise RuntimeError('Foreign or changed probe terminal')
        if int(archive.extractfile('probe.native-exit').read()) != terminal['probe_native_exit']:
            raise RuntimeError('Probe exit mismatch')
    folder = check/'termination-controls'; folder.mkdir()
    records = []
    def cloud(args):
        if args[:3] in (['compute', 'instances', 'describe'], ['compute', 'instances', 'stop']):
            if args[3] != VM: raise RuntimeError('Foreign VM target')
        elif args[:2] == ['compute', 'ssh']:
            if args[2] != VM: raise RuntimeError('Foreign SSH target')
        else: raise RuntimeError('Unapproved lifecycle operation')
        command = [SDK, *args, *FLAGS]
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try:
                out, err = child.communicate(timeout=30); break
            except subprocess.TimeoutExpired:
                print('Same termination command remains live', child.pid, flush=True)
        i = len(records)
        (folder/(str(i)+'.stdout')).write_bytes(out)
        (folder/(str(i)+'.stderr')).write_bytes(err)
        records.append(dict(argv=command, native_exit=child.returncode, utc=datetime.now(timezone.utc).isoformat()))
        (folder/'commands.json').write_text(json.dumps(records, indent=2)+'\n')
        if child.returncode: raise RuntimeError('Native termination command failed; preserve receipts')
        return out
    def describe():
        state = json.loads(cloud(['compute', 'instances', 'describe', VM, '--format=json(name,id,status,zone)']))
        if state['name'] != VM or str(state['id']) != VM_ID or state['zone'].rsplit('/', 1)[-1] != 'us-central1-a':
            raise RuntimeError('Unexpected resource identity')
        return state
    before = describe()
    if before['status'] == 'RUNNING':
        out = cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=ps -eo pid=,comm='])
        if any(line.split()[1] in ('lean', 'lake', 'python3') for line in out.decode().splitlines()):
            raise RuntimeError('Compiler or worker is still live')
        cloud(['compute', 'instances', 'stop', VM, '--async'])
    elif before['status'] != 'TERMINATED':
        raise RuntimeError('Observe the existing transition before proceeding')
    while True:
        final = describe()
        if final['status'] == 'TERMINATED': break
        print('Observing same dedicated probe shutdown', final['status'], flush=True)
        time.sleep(10)
    independent = describe()
    if independent['status'] != 'TERMINATED': raise RuntimeError('Independent termination not proven')
    result = dict(run=marker['run'], before=before, final=final, independent=independent,
        native_terminal=True, custody_verified_before_stop=True, other_vm_modified=False,
        probe_native_exit=terminal['probe_native_exit'], coverage_accepted=False)
    with (check/'vm-termination.json').open('x', encoding='utf-8') as output:
        json.dump(result, output, indent=2)
    print(json.dumps(result, indent=2), flush=True)

if __name__ == '__main__':
    main()
