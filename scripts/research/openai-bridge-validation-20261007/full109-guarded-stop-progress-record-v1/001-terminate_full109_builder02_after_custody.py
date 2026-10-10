"""Stop only the dedicated builder-02 after native terminal and exact custody."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import time
from full109_builder02_controller import ROOT, VM, VM_ID, audit_terminal, context, local_gates
from custody_checks import verify_local_custody
from finalize_builder02_bootstrap import SDK, FLAGS

def main():
    marker=json.loads((ROOT/'launch-once.json').read_bytes())
    check=Path(marker['preflight']).resolve(strict=True)
    if not check.is_relative_to((ROOT/'checks').resolve()): raise RuntimeError('Foreign check directory')
    receipt=json.loads((check/'terminal-custody.json').read_bytes())
    if receipt['run'] != marker['run']: raise RuntimeError('Foreign terminal receipt')
    custody=receipt['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    loaded,runner=context(); common=loaded['common']; local_gates(common,loaded)
    terminal=audit_terminal(custody['repository_path'],marker['run'],json.loads((ROOT/'capture-manifest.json').read_bytes()),common)
    if not terminal['native_terminal']: raise RuntimeError('Native terminal unproven')
    folder=check/'termination-controls'; folder.mkdir()
    records=[]
    def cloud(args):
        if args[:3] in (['compute','instances','describe'],['compute','instances','stop']):
            if args[3] != VM: raise RuntimeError('Foreign VM target')
        elif args[:2] == ['compute','ssh']:
            if args[2] != VM: raise RuntimeError('Foreign SSH target')
        else: raise RuntimeError('Unapproved termination operation')
        command=[SDK,*args,*FLAGS]
        process=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try: out,err=process.communicate(timeout=30); break
            except subprocess.TimeoutExpired: print('Same termination observation remains active',process.pid,flush=True)
        i=len(records); (folder/(str(i)+'.stdout')).write_bytes(out); (folder/(str(i)+'.stderr')).write_bytes(err)
        records.append(dict(argv=command,native_exit=process.returncode,utc=datetime.now(timezone.utc).isoformat()))
        (folder/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
        if process.returncode: raise RuntimeError('Native SDK termination command failed; retain receipts')
        return out
    def describe():
        state=json.loads(cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone)']))
        if state['name'] != VM or str(state['id']) != VM_ID or state['zone'].rsplit('/',1)[-1] != 'us-central1-a':
            raise RuntimeError('Unexpected GCP identity')
        return state
    before=describe()
    if before['status'] == 'RUNNING':
        out=cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=ps -eo pid=,comm='])
        if any(line.split()[1] in ('lean','lake','python3') for line in out.decode().splitlines()):
            raise RuntimeError('Compiler/worker process still present; VM retained')
        cloud(['compute','instances','stop',VM,'--async'])
    elif before['status'] != 'TERMINATED': raise RuntimeError('Unexpected transition; observe existing state')
    while True:
        final=describe()
        if final['status'] == 'TERMINATED': break
        print('Observing same dedicated VM shutdown',final['status'],flush=True); time.sleep(10)
    independent=describe()
    if independent['status'] != 'TERMINATED': raise RuntimeError('Independent termination not proven')
    result=dict(run=marker['run'],before=before,final=final,independent=independent,custody_verified_before_stop=True,
                native_terminal=True,compiler_green=terminal['compile_green'],other_vm_modified=False)
    with (check/'vm-termination.json').open('x') as stream: json.dump(result,stream,indent=2)
    print(json.dumps(result,indent=2),flush=True)

if __name__ == '__main__': main()
