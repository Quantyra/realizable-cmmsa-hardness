"""Use sufficient settled Full89/88 scopes under the existing recovery boot."""
import ast
import json
from pathlib import Path
import sys
import derive_full100_trace_recovery as parent
from custody_checks import digest

HERE = Path(__file__).parent
SCOPES = [
 ('full89-resource02', 5, '81813B3B53BC6112914005E65C4F41CCB96B9D5C0FC45D23D9E3E66B2AE11348',
  '0ECFA6657CEB08927A2ED197363DD2539A3319AC8F3945C02BB077AC67424A64'),
 ('full88-resource02', 5, 'D109D80CC27EA52FEFE01C9719DB539EB882A2BE63AAA0AF55182FC40EAE942B',
  '439CDC04EB513D3B6BDEC306482E74CC49CD43369E857D6CFBAF79B7E863C1D6'),
]

def outputs():
    assert digest(HERE/'derive_full100_trace_recovery.py') == '5C7C11DA245AB9C486C7064023C06ED6A625D15D75AE0ED4C752E6D2F7FC78EF'
    original = parent.SCOPES
    try:
        parent.SCOPES = SCOPES
        templates, custody = parent.outputs()
    finally:
        parent.SCOPES = original
    files = {}
    for name, text in templates.items():
        for old, new in [(1,5),(2,6)]:
            name = name.replace('repoint_v'+str(old), 'repoint_v'+str(new))
            text = text.replace('repoint-v'+str(old), 'repoint-v'+str(new)).replace('repoint_v'+str(old), 'repoint_v'+str(new))
        if name == 'full100_trace_recovery_vm_control.py':
            name = 'full100_trace_recovery_v2_vm_control.py'
            text = parent.once(text, "assert action in ('start','stop')", "assert action == 'stop', 'Existing recovery boot only; no additional start'")
            text = parent.once(text, 'assert len(executed)==4', 'assert len(executed)==2')
            text = parent.once(text,
                "{'/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v5','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v6','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v3','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v4'}",
                "{'/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v5','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v6'}")
            text = parent.once(text, '    loaded,runner,binding=ready()',
                "    loaded,runner,binding=ready()\n"
                "    boot=json.loads((ROOT/'recovery-boot-once.json').read_bytes())\n"
                "    original=Path(boot['controls']).resolve(strict=True)\n"
                "    assert original.is_relative_to((ROOT/'recovery-vm-controls').resolve())\n"
                "    started=json.loads((original/'receipt.json').read_bytes())\n"
                "    assert started['action']=='start' and started['before']['status']=='TERMINATED' and started['after']['status']=='RUNNING'\n"
                "    assert str(started['before']['id'])==VM_ID and str(started['after']['id'])==VM_ID")
        files[name] = text
    return files, custody

def main(write=False):
    files, custody = outputs(); rows = []
    for name, text in files.items():
        ast.parse(text); path = HERE/name; data = text.encode('utf-8')
        if write:
            with path.open('xb') as stream: stream.write(data)
        else: assert path.read_bytes() == data
        rows.append(dict(path=name,sha256=digest(path)))
    value = dict(schema='full100-trace-v2-sufficient-settled-cache-recovery',
        controls=rows,source_custody=custody,targets_GiB=[5,5],
        existing_boot_retained=True,new_start_forbidden=True,
        full100_current_workspace_and_canonical_cache_excluded_from_mutation=True,
        exact_per_file_plan_review_identity_and_reversible_transactions_unchanged=True,
        original_insufficient_scopes_preserved_unexecuted=True,
        compiler_invoked=False,cloud_operation=False,accepted=False)
    path = HERE/'full100-trace-recovery-v2-derivation.json'
    if write:
        with path.open('x',encoding='utf-8') as stream: json.dump(value,stream,indent=2);stream.write('\n')
    else: assert json.loads(path.read_bytes()) == value
    print('Five sufficient-scope recovery controls verified; existing lease only; no cloud operation')

if __name__ == '__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(bool(sys.argv[1:]))
