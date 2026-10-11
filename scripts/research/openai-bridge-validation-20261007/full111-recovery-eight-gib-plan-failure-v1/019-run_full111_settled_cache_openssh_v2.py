"""Continue only unattempted recovery operations after the preserved SDK crash."""
import base64
from datetime import datetime, timezone
import json
from pathlib import Path
import shlex
import sys
from custody_checks import digest
from full111_builder02_controller import ROOT, context, local_gates
from run_full111_settled_cache_recovery_v1 import settled
from full112_dedicated_openssh_v1 import Session

HERE = Path(__file__).resolve().parent
RECOVERY = ROOT/'settled-cache-recovery-v1'
NUMBERS = [111,96,97,98]


def main(action):
    assert action in ('plan','execute')
    settled()
    loaded, _ = context(); local_gates(loaded['common'], loaded)
    failure = ROOT/'research-resume-20261011/20261011T042854525502Z-3c1895f34b07'
    record = json.loads((failure/'command.json').read_bytes())
    assert record['native_exit'] == 1
    for stream in ('stdout','stderr'): assert digest(failure/stream) == record[stream+'_sha256']
    commands = json.loads((RECOVERY/'20261011T043228243781Z/commands.json').read_bytes())
    assert [r['native_exit'] for r in commands] == [0,0,0,3221225477]
    assert commands[-1]['argv'][5].startswith('--command=sha256sum ')
    assert not any('--plan' in arg or '--execute' in arg for row in commands for arg in row['argv'])
    scopes = json.loads((HERE/'full111-settled-cache-recovery-derivation-v1.json').read_bytes())['scopes']
    assert [r['number'] for r in scopes] == NUMBERS
    folder = RECOVERY/('openssh-'+action+'-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    if action == 'execute':
        preservation = HERE/'full111-recovery-plans-openssh-record-v2/index.json'
        preserved = json.loads(preservation.read_bytes())
        assert preserved['all_four_plans_verified'] and not preserved['execution_included']
        for row in preserved['files']:
            assert digest(preservation.parent/row['copy']) == row['sha256']
        (RECOVERY/'execution-request-once-v2.json').open('x').write(json.dumps(dict(control=str(folder),plan_custody_sha256=digest(preservation)))+'\n')
    results = []
    with Session(folder/'transport') as session:
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer')
        for scope in scopes:
            number = scope['number']; source = HERE/scope['helper']; remote = scope['remote_control']
            assert digest(source) == scope['helper_sha256']
            (folder/source.name).open('xb').write(source.read_bytes())
            plan_record = None
            if action == 'execute':
                candidates = []
                for p in RECOVERY.glob('*/operation-*.json'):
                    row = json.loads(p.read_bytes())
                    if row['number'] == number and row['action'] == 'plan': candidates.append(row)
                assert len(candidates) == 1
                plan_record = candidates[0]
                assert digest(Path(plan_record['local_result'])) == plan_record['result_sha256']
            preamble = "import base64,hashlib,importlib.util,json\nfrom pathlib import Path\n"
            preamble += 'root=Path('+repr(remote)+')\nsource=root/'+repr(source.name)+'\n'
            if action == 'plan':
                if number == 111:
                    preamble += 'assert sorted(p.name for p in root.iterdir())==['+repr(source.name)+']\n'
                else:
                    preamble += "root.mkdir(exist_ok=False)\nsource.open('xb').write(base64.b64decode("+repr(base64.b64encode(source.read_bytes()).decode())+"))\n"
            preamble += 'assert hashlib.sha256(source.read_bytes()).hexdigest().upper()=='+repr(scope['helper_sha256'])+'\n'
            preamble += "spec=importlib.util.spec_from_file_location('exact_recovery',source)\nmodule=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)\nmodule.guards()\n"
            if action == 'plan':
                preamble += "assert not (root/'plan.json').exists() and not (root/'execute-once.json').exists()\n(root/'plan-request-once-v2.json').open('x').write('original planner did not invoke plan; first invocation via OpenSSH\\n')\nmodule.plan()\n"
            else:
                preamble += 'assert hashlib.sha256((root/\'plan.json\').read_bytes()).hexdigest().upper()=='+repr(plan_record['result_sha256'])+'\nmodule.execute()\n'
            session.python(preamble)
            name = 'plan.json' if action == 'plan' else 'receipt.json'
            hash_path = session.ssh('sha256sum '+shlex.quote(remote+'/'+name))
            pin = hash_path.read_text().split()[0].upper()
            raw_path = session.ssh('cat '+shlex.quote(remote+'/'+name))
            assert digest(raw_path) == pin
            value = json.loads(raw_path.read_bytes())
            if action == 'plan':
                assert not value['executed'] and not value['compiler_invoked']
                assert value['original_archive_sha256'] == scope['archive_sha256']
                assert value['old_root'] == '/home/dfredriksen_quantyra_org/'+scope['run']+'/.lake/packages'
                assert value['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
                rows = value['rows']; assert rows and len({r['relative'] for r in rows}) == len(rows)
                for row in rows:
                    path = Path(row['relative'])
                    assert not path.is_absolute() and '..' not in path.parts and row['bytes'] > 0
                    assert path.name.endswith(('.olean','.olean.private','.olean.server','.ilean'))
                    assert {'.lake','build','lib','lean'} <= set(path.parts)
                    assert len(row['sha256']) == 64 and all(c in '0123456789ABCDEF' for c in row['sha256'])
                assert sum(r['allocated_bytes'] for r in rows) == value['allocated_bytes'] >= scope['target_bytes']
            else:
                plan = json.loads(Path(plan_record['local_result']).read_bytes())
                assert value['applied'] == plan['rows']
                assert value['content_identity_verified_after_repoint'] and value['reversible_by_copying_identical_canonical_bytes']
                assert value['disk_after_bytes'] > value['disk_before_bytes']
                assert not any(value[k] for k in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'))
            result = dict(action=action,number=number,local_result=str(raw_path),result_sha256=pin,
                helper_sha256=scope['helper_sha256'],remote_control=remote,compiler_invoked=False,VM_power_operation=False,
                transport='existing-trusted-host-key-IAP-OpenSSH',original_failed_controller_replayed=False)
            (folder/f'operation-{number}.json').open('x').write(json.dumps(result,indent=2)+'\n')
            results.append(result); print(json.dumps(result),flush=True)
    local_gates(loaded['common'], loaded)
    (folder/'result.json').open('x').write(json.dumps(dict(operations=results,original_operations_settled=True,compiler_invoked=False),indent=2)+'\n')
    print(json.dumps(dict(folder=str(folder),operations=len(results),native_exit=0)),flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
