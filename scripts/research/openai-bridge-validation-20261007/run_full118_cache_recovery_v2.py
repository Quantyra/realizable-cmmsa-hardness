"""One retained controller per recovery phase; only exact settled object copies."""
import base64
from datetime import datetime, timezone
import json
from pathlib import Path
import shlex
import sys
from custody_checks import digest
from full117_builder02_controller import ROOT as PARENT
from full118_builder02_controller import ROOT, context, local_gates
from full117_capture_gates import validate_successor as parent_gate
from custody_checks import verify_local_custody
from full114_dedicated_openssh_v2 import Session

HERE = Path(__file__).resolve().parent

def settled():
    from start_inspect_full118_owned_capacity_v3 import verify_cleanup_receipt
    verify_cleanup_receipt()
    import full118_authorized39_custody_v2 as actual
    actual.configured_guard().documents()
    parent_gate()
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
    assert marker['run']==receipt['run']==stop['run']=='cmmsa_a8_output_20261011T231800Z_f8f19b01'
    assert receipt['terminal']['native_terminal'] and stop['custody_verified_before_stop']
    assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    c=receipt['custody'];verify_local_custody(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes'])
    assert not (ROOT/'launch-once.json').exists()
    return stop
RECOVERY = PARENT / 'settled-cache-recovery-v1'
DERIVATION = HERE / 'full118-cache-recovery-derivation-v4.json'


def scopes():
    value = json.loads(DERIVATION.read_bytes())
    result = value['scopes']
    assert result and len({s['number'] for s in result}) == len(result)
    for row in result:
        assert digest(HERE / row['helper']) == row['helper_sha256']
    return result


def operation(number, action):
    matches = []
    for path in RECOVERY.glob('openssh-*/*operation-*.json'):
        row = json.loads(path.read_bytes())
        if row['number'] == number and row['action'] == action:
            assert digest(Path(row['local_result'])) == row['result_sha256']
            matches.append((path, row))
    assert len(matches) == 1, (number, action, len(matches))
    return matches[0]


def verified_plans():
    seen = set(); summaries = []
    for scope in scopes():
        _, record = operation(scope['number'], 'plan')
        value = json.loads(Path(record['local_result']).read_bytes())
        assert not value['executed'] and not value['compiler_invoked']
        assert value['original_archive_sha256'] == scope['archive_sha256']
        assert value['old_root'] == '/home/dfredriksen_quantyra_org/' + scope['run'] + '/.lake/packages'
        assert value['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
        assert value['rows'] and sum(r['allocated_bytes'] for r in value['rows']) == value['allocated_bytes'] >= scope['target_bytes']
        for row in value['rows']:
            path = Path(row['relative']); key = (scope['run'], row['relative'])
            assert not path.is_absolute() and '..' not in path.parts and key not in seen
            if scope['kind'] in ('lean-large', 'lean-small'):
                assert path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean'))
                assert {'.lake', 'build', 'lib', 'lean'} <= set(path.parts)
                assert (row['bytes'] >= 65536) if scope['kind'] == 'lean-large' else (0 < row['bytes'] < 65536)
            else:
                assert scope['kind'] == 'generated' and row['bytes'] > 0
                generated_ir = {'.lake', 'build', 'ir'} <= set(path.parts) and path.name.endswith(('.c', '.c.o.export', '.setup.json'))
                generated_lean_ir = {'.lake', 'build', 'lib', 'lean'} <= set(path.parts) and path.name.endswith('.ir')
                generated_bin = path.as_posix() in ('batteries/.lake/build/bin/runLinter', 'mathlib/.lake/build/bin/cache')
                assert generated_ir or generated_lean_ir or generated_bin
            assert row['bytes'] > 0 and len(row['sha256']) == 64
            seen.add(key)
        summaries.append(dict(number=scope['number'], rows=len(value['rows']), allocated_bytes=value['allocated_bytes'], plan_sha256=record['result_sha256']))
    return summaries


def main(action):
    assert action in ('plan', 'execute')
    settled(); loaded, _ = context(); local_gates(loaded['common'], loaded)
    assert __import__('shutil').disk_usage(ROOT).free >= 1803550720
    selected = scopes()
    assert not (ROOT / 'launch-once.json').exists()
    RECOVERY.mkdir(parents=True,exist_ok=True)
    folder = RECOVERY / ('openssh-' + action + '-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    (folder / DERIVATION.name).write_bytes(DERIVATION.read_bytes())
    if action == 'execute':
        summaries = verified_plans()
        custody = HERE / 'full118-recovery-additive-plans-record-v2/index.json'
        preserved = json.loads(custody.read_bytes())
        assert preserved['all_selected_plans_verified'] and preserved['scopes'] == summaries
        assert not preserved['execution_included']
        payload = preserved['payload']
        assert digest(custody.parent / payload['file']) == payload['sha256']
        (RECOVERY / 'execution-request-once-additive-v2.json').open('x').write(json.dumps(dict(control=str(folder), plan_custody_sha256=digest(custody))) + '\n')
    results = []
    with Session(folder / 'transport') as session:
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer')
        for scope in selected:
            number = scope['number']; source = HERE / scope['helper']; remote = scope['remote_control']
            assert digest(source) == scope['helper_sha256']
            (folder / source.name).open('xb').write(source.read_bytes())
            guest = "import base64,hashlib,importlib.util,json\nfrom pathlib import Path\n"
            guest += 'root=Path(' + repr(remote) + ')\nsource=root/' + repr(source.name) + '\n'
            if action == 'plan':
                guest += "root.mkdir(exist_ok=False)\nsource.open('xb').write(base64.b64decode(" + repr(base64.b64encode(source.read_bytes()).decode()) + "))\n"
            guest += 'assert hashlib.sha256(source.read_bytes()).hexdigest().upper()==' + repr(scope['helper_sha256']) + '\n'
            guest += "spec=importlib.util.spec_from_file_location('exact_recovery',source)\nmodule=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)\nmodule.guards()\n"
            if action == 'plan':
                guest += "assert not (root/'plan.json').exists() and not (root/'execute-once.json').exists()\n(root/'plan-request-once.json').open('x').write('first exact Full118 recovery plan invocation\\n')\nmodule.plan()\n"
            else:
                _, pr = operation(number, 'plan')
                guest += "assert hashlib.sha256((root/'plan.json').read_bytes()).hexdigest().upper()==" + repr(pr['result_sha256']) + '\nmodule.execute()\n'
            session.python(guest)
            name = 'plan.json' if action == 'plan' else 'receipt.json'
            pin = session.ssh('sha256sum ' + shlex.quote(remote + '/' + name)).read_text().split()[0].upper()
            raw = session.ssh('cat ' + shlex.quote(remote + '/' + name))
            assert digest(raw) == pin
            value = json.loads(raw.read_bytes())
            if action == 'execute':
                plan = json.loads(Path(pr['local_result']).read_bytes())
                assert value['applied'] == plan['rows']
                assert value['content_identity_verified_after_repoint'] and value['reversible_by_copying_identical_canonical_bytes']
                assert value['disk_after_bytes'] > value['disk_before_bytes']
                assert not any(value[k] for k in ('warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked'))
            record = dict(action=action, number=number, local_result=str(raw), result_sha256=pin,
                helper_sha256=scope['helper_sha256'], remote_control=remote,
                compiler_invoked=False, power_operation=False, original_operation_replayed=False)
            (folder / f'operation-{number}.json').open('x').write(json.dumps(record, indent=2) + '\n')
            results.append(record); print(json.dumps(record), flush=True)
    if action == 'plan':
        verified_plans()
    local_gates(loaded['common'], loaded)
    (folder / 'result.json').open('x').write(json.dumps(dict(operations=results, compiler_invoked=False, native_exit=0), indent=2) + '\n')
    print(json.dumps(dict(folder=str(folder), operations=len(results), native_exit=0)), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
