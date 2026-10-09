"""Prepare recovery-only controls after native custody; no cloud execution."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
SOURCE = 'full97_cache_repoint_v1.py'
DRIVER = 'run_full95_trace_cache_repoint.py'
LEASE = 'full97_recovery_vm_control.py'
PINS = {
    SOURCE: '3B6CE8138EDEC3E0FF953B59E1F98106BE67AC669BB51F09480538C900D28045',
    DRIVER: '8007ED98BE03FF702F5DDC0C16C1C53FD116F2D2B0570133A29F653F80D389F6',
    LEASE: 'C82FEFA4370D002088C556FFA3C81DE7B80A4449452474C1C0750E06E375ACB8',
}
SCOPES = [
    ('cmmsa_a8_output_20261009T050952Z_3a6b1f17',
     '39CA9EDB48C35171FC878ED7301456C1D7C0BC5BCDF27F47FE96798040E5779D',
     '693105513ECC569B34F027FC31FEC85B2C7747A7338CFDFF7CBE9CBE74E773E4'),
    ('cmmsa_a8_output_20261009T040701Z_db82b17d',
     'DB9FD9AA2B961BC2B05FB23B5EC6FC18C9B7A97BE022C70928445015464C62D1',
     'BFD42A52C5F8C63421A7A5FEBF7B52F3958762A6D93C328525913CC4702B5341'),
]


def once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError('Unexpected pinned recovery template: ' + old)
    return text.replace(old, new, 1)


def outputs():
    for name, pin in PINS.items():
        if digest(HERE / name) != pin:
            raise RuntimeError('Recovery parent drift: ' + name)
    files = {}
    for i, (run, manifest, archive) in enumerate(SCOPES, 1):
        text = (HERE / SOURCE).read_text(encoding='utf-8')
        text = text.replace('settled Full95', 'settled Full97' if i == 1 else 'settled Full96')
        text = text.replace('Full95', 'Full97' if i == 1 else 'Full96')
        text = text.replace('Original failed evidence archive', 'Original native evidence archive')
        text = once(text, "RUN = 'cmmsa_a8_output_20261009T023928Z_13a1218e'", "RUN = " + repr(run))
        text = once(text, "CONTROL = HOME / 'full97-cache-repoint-v1'",
                    "CONTROL = HOME / 'full97-trace-cache-repoint-v" + str(i) + "'")
        text = once(text, "MANIFEST_SHA = '0D7BC8E82E058AEE23B7366E0DE64565A74D978D7F65D963995717B795971732'", 'MANIFEST_SHA = ' + repr(manifest))
        text = once(text, "ARCHIVE_SHA = 'E48640AC66338FE792BED8400BF24F7EC947C4B80CB1687CC3992CFACE126EE2'", 'ARCHIVE_SHA = ' + repr(archive))
        text = text.replace('full97-spectral-bridge-utf8-section-repair-resource02-launch-once.json',
                            'full97-consumption-v1-launch-once.json')
        text = text.replace('Full97 native launch already exists', 'Full97 trace launch already exists')
        text = text.replace('full95-settled-dependency-cache-repoint', 'full97-trace-settled-dependency-cache-repoint')
        files['full97_trace_cache_repoint_v' + str(i) + '.py'] = text
        text = (HERE / DRIVER).read_text(encoding='utf-8').replace('full95', 'full97').replace('Full95', 'Full97')
        text = once(text, 'from full97_consumption_controller import ROOT',
                    'from full97_consumption_controller import ROOT, ready')
        text = once(text, "    validate_successor()\n    loaded, runner = context()\n    local_gates(loaded['common'], loaded)",
                    '    loaded, runner, binding = ready()')
        text = text.replace('full97-trace-cache-repoint-v1', 'full97-trace-cache-repoint-v' + str(i))
        text = text.replace('full97_trace_cache_repoint.py', 'full97_trace_cache_repoint_v' + str(i) + '.py')
        files['run_full97_trace_cache_repoint_v' + str(i) + '.py'] = text
    text = (HERE / LEASE).read_text(encoding='utf-8')
    text = once(text, 'from full97_builder02_controller import ROOT,VM,VM_ID,context,local_gates',
                'from full97_consumption_controller import ROOT,VM,VM_ID,ready')
    text = once(text, "    validate_successor();loaded,runner=context();local_gates(loaded['common'],loaded)",
                '    loaded,runner,binding=ready()')
    text = text.replace('Native attempt exists; recovery lease forbidden', 'Trace attempt exists; recovery lease forbidden')
    text = once(text, "        receipts=list((ROOT/'cache-repoint-controls').glob('*/operation.json'))",
                "        receipts=sorted((ROOT/'cache-repoint-controls').glob('*/operation.json'))")
    text = once(text, "        call(['compute','instances','start',VM]);after=state();assert after['status']=='RUNNING'",
                "        call(['compute','instances','start',VM]);after=state();assert after['status']=='RUNNING'\n"
                "        call(['compute','ssh',VM,'--tunnel-through-iap','--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])")
    text = once(text, '        assert len(executed)==2',
                "        assert len(executed)==2\n"
                "        assert {r['remote_control'] for r in executed}=={'/home/dfredriksen_quantyra_org/full97-trace-cache-repoint-v1','/home/dfredriksen_quantyra_org/full97-trace-cache-repoint-v2'}\n"
                "        assert json.loads(Path(executed[-1]['local_result']).read_bytes())['disk_after_bytes']>=40*1024**3")
    files['full97_trace_recovery_vm_control.py'] = text
    return files


def main(verify=False):
    rows = []
    for name, text in outputs().items():
        ast.parse(text, filename=name)
        path = HERE / name
        data = text.encode()
        if verify:
            if path.read_bytes() != data:
                raise RuntimeError('Trace recovery derivation drift')
        else:
            with path.open('xb') as output:
                output.write(data)
        rows.append(dict(path=name, sha256=digest(path)))
    value = dict(schema='full97-qualified-native-bound-trace-recovery-v1',
        parent_pins=PINS, controls=rows, scopes=SCOPES, target_GiB_each=5,
        exact_qualified_native_and_independent_termination_required=True,
        only_duplicate_dependency_objects_repointed=True,
        source_project_object_canonical_warm_and_archive_bytes_preserved=True,
        plan_review_before_mutation_required=True, compiler_invoked=False,
        cloud_operation=False, accepted=False)
    receipt = HERE / 'full97-trace-recovery-derivation.json'
    if verify:
        if json.loads(receipt.read_bytes()) != json.loads(json.dumps(value)):
            raise RuntimeError('Trace recovery derivation receipt drift')
    else:
        with receipt.open('x', encoding='utf-8', newline='\n') as output:
            json.dump(value, output, indent=2)
            output.write('\n')
    print('Full97 trace recovery controls ' + ('verified' if verify else 'prepared')
          + '; no compiler/cloud operation')


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--verify']):
        raise SystemExit('Use initial derivation or --verify')
    main(sys.argv[1:] == ['--verify'])
