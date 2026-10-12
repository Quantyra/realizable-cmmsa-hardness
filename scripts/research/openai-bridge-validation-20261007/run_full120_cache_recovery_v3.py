"""One retained controller per recovery phase; only exact settled object copies."""
import base64
from datetime import datetime, timezone
import json
from pathlib import Path
import shlex
import sys
from custody_checks import digest
from full119_builder02_controller import ROOT as PARENT
from full120_builder02_controller import ROOT, context, local_gates
from full119_capture_gates import validate_successor as parent_gate
from custody_checks import verify_local_custody
from full114_dedicated_openssh_v2 import Session

HERE = Path(__file__).resolve().parent

def settled():
    from start_inspect_full120_owned_capacity_v1 import verify_cleanup_receipt
    verify_cleanup_receipt()
    import full119_authorized16_nested_custody_v3 as actual
    actual.configured_guard().documents()
    parent_gate()
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
    assert marker['run']==receipt['run']==stop['run']=='cmmsa_a8_output_20261012T074255Z_4527aeb2'
    assert receipt['terminal']['native_terminal'] and stop['custody_verified_before_stop']
    assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    c=receipt['custody'];verify_local_custody(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes'])
    assert not (ROOT/'launch-once.json').exists()
    return stop
RECOVERY = ROOT / 'settled-generated-recovery-v1'
DERIVATION = HERE / 'full120-generated-recovery-derivation-v1.json'


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
    seen=set();summaries=[]
    for scope in scopes():
        _,record=operation(scope['number'],'plan');value=json.loads(Path(record['local_result']).read_bytes())
        assert not value['executed'] and not value['compiler_invoked'] and value['original_archive_sha256']==scope['archive_sha256']
        suffix='/.lake/build' if scope['kind']=='project-ir' else '/.lake/packages'
        assert value['old_root']=='/home/dfredriksen_quantyra_org/'+scope['run']+suffix
        assert value['canonical_root']=='/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24'+suffix
        assert value['rows'] and sum(r['allocated_bytes'] for r in value['rows'])==value['allocated_bytes']>=scope['target_bytes']
        for row in value['rows']:
            path=Path(row['relative']);key=(scope['run'],suffix,row['relative']);assert not path.is_absolute() and '..' not in path.parts and key not in seen and row['bytes']>0 and len(row['sha256'])==64
            if scope['kind']=='lean-large':assert path.name.endswith(('.olean','.olean.private','.olean.server','.ilean')) and {'.lake','build','lib','lean'}<=set(path.parts) and row['bytes']>=65536
            elif scope['kind']=='project-ir':assert ('ir' in path.parts and path.name.endswith(('.c','.c.o.export','.setup.json'))) or ({'lib','lean'}<=set(path.parts) and path.name.endswith('.ir'))
            else:
                assert scope['kind']=='generated'
                assert ({'.lake','build','ir'}<=set(path.parts) and path.name.endswith(('.c','.c.o.export','.setup.json'))) or ({'.lake','build','lib','lean'}<=set(path.parts) and path.name.endswith('.ir')) or path.as_posix() in ('batteries/.lake/build/bin/runLinter','mathlib/.lake/build/bin/cache')
            seen.add(key)
        summaries.append(dict(number=scope['number'],rows=len(value['rows']),allocated_bytes=value['allocated_bytes'],plan_sha256=record['result_sha256']))
    return summaries

def verify_describe_only_auth_failure():
    failure = HERE / 'full120-recovery-transport-auth-failure-v1/index.json'
    assert digest(failure) == '5084FCD9EC7CC05B085D6669C63580EE5FAE997F347EE198583E4F70B98252BE'
    value = json.loads(failure.read_bytes())
    assert value['original_handle'] == 54362 and value['native_exit'] == 1
    assert not value['guest_execution_started'] and value['interactive_reauthentication_required']
    assert value['account'] == 'dfredriksen@quantyra.org'
    assert digest(failure.parent / value['payload']['file']) == value['payload']['sha256']
    for row in value['files']:
        path=Path(row['original']); assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
    marker = RECOVERY / 'execution-request-once.json'
    previous = json.loads(marker.read_bytes())
    folder = Path(previous['control'])
    assert folder.resolve() == (RECOVERY / 'openssh-execute-20261012T111414605077Z').resolve()
    commands = json.loads((folder/'transport/commands.json').read_bytes())
    assert len(commands)==1 and commands[0]['native_exit']==1
    assert commands[0]['argv'][1:5]==['compute','instances','describe','quantyra-lean-builder-02']
    assert '--account=dfredriksen@quantyra.org' in commands[0]['argv']
    assert not (folder/'transport/tunnel-start.json').exists()
    assert not list(RECOVERY.glob('openssh-execute-*/operation-*.json'))
    assert previous['plan_custody_sha256']==digest(HERE/'full120-recovery-plans-record-v1/index.json')
    assert digest(folder/'run_full120_cache_recovery_v2.py')=='4A2918D8F6C29C5B061E02584429A503A11E3CEA4207D20258F16547082B1AB6'
    return dict(original_marker_sha256=digest(marker),auth_failure_custody_sha256=digest(failure),prior_transport_describe_only=True)


def main(action):
    assert action == 'execute', 'v3 is execute-only; frozen v1 plans and exact describe-only auth failure are required'
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
        custody = HERE / 'full120-recovery-plans-record-v1/index.json'
        preserved = json.loads(custody.read_bytes())
        assert preserved['all_selected_plans_verified'] and preserved['scopes'] == summaries
        assert not preserved['execution_included']
        payload = preserved['payload']
        assert digest(custody.parent / payload['file']) == payload['sha256']
        prior=verify_describe_only_auth_failure()
        (RECOVERY / 'execution-resume-after-reauth-request-once-v1.json').open('x').write(json.dumps(dict(control=str(folder),plan_custody_sha256=digest(custody),prior=prior,original_marker_preserved=True))+'\n')
    results = []
    with Session(folder / 'transport') as session:
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; systemctl is-active quantyra-idle-shutdown.timer')
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
                guest += "assert not (root/'plan.json').exists() and not (root/'execute-once.json').exists()\n(root/'plan-request-once.json').open('x').write('first exact Full120 recovery plan invocation\\n')\nmodule.plan()\n"
            else:
                _, pr = operation(number, 'plan')
                guest += "assert hashlib.sha256((root/'plan.json').read_bytes()).hexdigest().upper()==" + repr(pr['result_sha256']) + '\n'
                guest += "import stat\nold,canonical=module.guards()\nplan=json.loads((root/'plan.json').read_bytes())\nassert plan['old_root']==str(old) and plan['canonical_root']==str(canonical)\n"
                guest += 'kind=' + repr(scope['kind']) + '\n'
                guest += "seen=set()\nfor row in plan['rows']:\n rel=Path(row['relative'])\n assert not rel.is_absolute() and '..' not in rel.parts and row['relative'] not in seen\n seen.add(row['relative'])\n if kind=='lean-large':\n  assert rel.name.endswith(('.olean','.olean.private','.olean.server','.ilean')) and {'.lake','build','lib','lean'}<=set(rel.parts) and row['bytes']>=65536\n elif kind=='project-ir':\n  assert ('ir' in rel.parts and rel.name.endswith(('.c','.c.o.export','.setup.json'))) or ({'lib','lean'}<=set(rel.parts) and rel.name.endswith('.ir'))\n else:\n  assert kind=='generated'\n  assert ({'.lake','build','ir'}<=set(rel.parts) and rel.name.endswith(('.c','.c.o.export','.setup.json'))) or ({'.lake','build','lib','lean'}<=set(rel.parts) and rel.name.endswith('.ir')) or rel.as_posix() in ('batteries/.lake/build/bin/runLinter','mathlib/.lake/build/bin/cache')\n path,destination=old/rel,canonical/rel\n assert not path.is_symlink() and path.resolve().is_relative_to(old) and destination.resolve().is_relative_to(canonical)\n info=path.stat();target=destination.stat()\n assert stat.S_ISREG(info.st_mode) and info.st_nlink==1 and stat.S_ISREG(target.st_mode)\n assert info.st_size==target.st_size==row['bytes']\n assert module.digest(path)==module.digest(destination)==row['sha256']\nassert hashlib.sha256((root/'plan.json').read_bytes()).hexdigest().upper()==" + repr(pr['result_sha256']) + "\nmodule.execute()\n"
            session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active')
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
                generated_paths_repointed_with_identical_content=(action=='execute'),
                project_source_and_project_proof_objects_excluded=True,
                legacy_source_or_project_object_flag_means_content_not_path_type=True,
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
