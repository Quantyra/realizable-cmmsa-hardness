"""Offline transport boundary tests; no cloud or Lean invocation."""
import ast
from datetime import datetime,timezone
import json
from pathlib import Path
import sys
from custody_checks import digest
from full112_dedicated_openssh_v2 import Session
import full112_openssh_control_v1 as adapter

HERE=Path(__file__).resolve().parent


def main():
    folder=HERE/('full112-openssh-control-validation-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    names=['full112_dedicated_openssh_v2.py','full112_openssh_control_v1.py','run_full112_native_openssh_v1.py',
        'stage_full112_after_recovery_openssh_v2.py','audit_full111_settled_cache_recovery_v2.py',Path(__file__).name]
    pins={}
    for n in names:
        p=HERE/n;ast.parse(p.read_text(encoding='utf-8'));(folder/n).write_bytes(p.read_bytes());pins[n]=digest(p)
    outcomes=[]
    session=Session(folder/'rejected-nonzero')
    try:session.call([sys.executable,'-B','-c',"import sys;sys.stdout.buffer.write(b'original-out');sys.stderr.buffer.write(b'original-err');sys.exit(7)"])
    except AssertionError:pass
    else:raise AssertionError('Nonzero incorrectly accepted')
    assert session.records[-1]['native_exit']==7
    assert Path(session.records[-1]['stdout_path']).read_bytes()==b'original-out'
    assert Path(session.records[-1]['stderr_path']).read_bytes()==b'original-err'
    outcomes.append('nonzero rejected with exact complete raw streams')
    session=Session(folder/'retained-nonzero')
    session.call([sys.executable,'-B','-c','raise SystemExit(7)'],allow_failure=True)
    assert session.records[-1]['native_exit']==7;outcomes.append('allowed native nonzero retained as nonzero')
    destination=folder/'direct-custody.bin';session=Session(folder/'direct-custody')
    p=session.call([sys.executable,'-B','-c','import sys;sys.stdout.buffer.write(bytes(range(256))*32)'],output_path=destination)
    assert p==destination and p.read_bytes()==bytes(range(256))*32
    assert session.records[-1]['stdout_sha256']==digest(destination);outcomes.append('direct custody preserves arbitrary binary bytes')
    class Parent:
        authenticated=True
        def cloud(self,*a,**kw):raise AssertionError('Unexpected delegation')
    class Runner:Control=Parent
    control=adapter.install(Runner).Control()
    bad=[['compute','ssh','foreign','--tunnel-through-iap','--command=true'],
         ['compute','instances','describe','foreign'],
         ['compute','scp','quantyra-lean-builder-02:/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261011T000000Z_12345678_evidence.tar.gz',str(folder/'outside-custody.tar.gz'),'--tunnel-through-iap']]
    for args in bad:
        try:control.cloud(args)
        except AssertionError:pass
        else:raise AssertionError('Foreign target or custody escape accepted')
    assert not adapter.SESSIONS;outcomes.append('foreign VM and destination escape rejected before transport')
    result=dict(source_snapshots=pins,outcomes=outcomes,all_offline_checks_passed=True,
        cloud_action=False,compiler_invoked=False,synthetic_not_native_evidence=True)
    (folder/'result.json').open('x').write(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(folder=str(folder),checks=len(outcomes),all_offline_checks_passed=True)),flush=True)


if __name__=='__main__':main()
