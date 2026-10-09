"""Reproduce guarded recovery of settled copies, never current Full100 objects."""
import ast
import json
from pathlib import Path
import sys
import tarfile
from custody_checks import digest, verify_local_custody

HERE = Path(__file__).parent
PINS = {
 'full100_cache_repoint_v1.py': 'C29A9BC269BAFB04FB231D0E372B7DA0B4F65136834C988185EEAEA1E5A78762',
 'run_full97_trace_cache_repoint_v1.py': 'CA698B63C718F7D6D2EBF887C17B8595F1F98939528266D7AF474F7FD661167C',
 'full97_trace_recovery_vm_control.py': 'EB166203AB9422992FCE3526338C38D3B66D4D718184B41AA448527F27BA97FF',
}
SCOPES = [
 ('full98-actual-matrix-fourier-bridge-resource02', 3,
  '31DE9C6EEA69FF3A503CE53AAD23A53434D928BF7104E5FCF58613C71B65CD7D',
  '274E5E941CC6502A84299D29CD608457F5F1FE5B2A98593D6C72D24F057321AA'),
 ('full99-matrix-fourier-bullet-repair-resource02', 3,
  '98537853DEE1623F6455AD1FA75116FE65FC47134B061EEE3F93E3FE0EC418EF',
  'C18468B03B793BF120B89A266622718FF299F082FF536B8D4D85A421A17C94BA'),
 ('full96-spectral-orbit-contract-bridge-resource02', 3,
  'DB9FD9AA2B961BC2B05FB23B5EC6FC18C9B7A97BE022C70928445015464C62D1',
  'BFD42A52C5F8C63421A7A5FEBF7B52F3958762A6D93C328525913CC4702B5341'),
 ('full90-material-resource02', 2,
  'E2D3B6F5BAF7C45570F81FF7E61019FE9763E25494E22AD1E09E69580DC975BB',
  '71133F9AB610A4DE48C39E3AE5320216C8EDE1D4E6F4F9AB9C9B897B92206246'),
]

def once(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new, 1)

def outputs():
    for name, pin in PINS.items(): assert digest(HERE/name) == pin
    files, custody_rows = {}, []
    for i, (resource, target, manifest_pin, archive_pin) in enumerate(SCOPES, 1):
        base = Path('C:/Users/dfred/.quantyra/builder02')/resource
        marker = json.loads((base/'launch-once.json').read_bytes())
        run = marker['run']; check = Path(marker['preflight'])
        terminal = json.loads((check/'terminal-custody.json').read_bytes())
        custody = terminal['custody']
        assert custody['remote_sha256'] == archive_pin
        verify_local_custody(custody['short_path'], custody['repository_path'], archive_pin, custody['bytes'])
        stop = json.loads((check/'vm-termination.json').read_bytes())
        assert stop['independent']['status'] == 'TERMINATED'
        assert str(stop['independent']['id']) == '7237681467779354904'
        with tarfile.open(custody['repository_path']) as archive:
            import hashlib
            assert hashlib.sha256(archive.extractfile('capture-manifest.json').read()).hexdigest().upper() == manifest_pin
            assert json.loads(archive.extractfile('source-before.json').read()) == json.loads(archive.extractfile('source-after.json').read())
            exits = [int(archive.extractfile('stage-'+str(j)+'.native-exit').read()) for j in range(7)]
        custody_rows.append(dict(resource=resource, run=run, manifest_sha256=manifest_pin,
            archive_sha256=archive_pin, termination_sha256=digest(check/'vm-termination.json'),
            two_copy_custody_verified=True, sources_preserved=True, stage_exits=exits))
        remote = 'full100-trace-cache-repoint-v'+str(i)
        text = (HERE/'full100_cache_repoint_v1.py').read_text(encoding='utf-8')
        text = once(text, "RUN = 'cmmsa_a8_output_20261009T080216Z_9e248b8e'", 'RUN = '+repr(run))
        text = once(text, "CONTROL = HOME / 'full100-cache-repoint-v1'", 'CONTROL = HOME / '+repr(remote))
        text = once(text, "MANIFEST_SHA = '98537853DEE1623F6455AD1FA75116FE65FC47134B061EEE3F93E3FE0EC418EF'", 'MANIFEST_SHA = '+repr(manifest_pin))
        text = once(text, "ARCHIVE_SHA = 'C18468B03B793BF120B89A266622718FF299F082FF536B8D4D85A421A17C94BA'", 'ARCHIVE_SHA = '+repr(archive_pin))
        text = once(text, 'TARGET = 5 * 1024**3', 'TARGET = '+str(target)+' * 1024**3')
        text = text.replace('full100-matrix-fourier-bullet-repair-resource02-launch-once.json', 'full100-consumption-v2-launch-once.json')
        text = text.replace('settled Full99', 'settled '+resource.split('-')[0]).replace('Settled Full99', 'Settled '+resource.split('-')[0])
        text = text.replace('Full97 launch already exists', 'Full100 v2 trace launch already exists')
        files['full100_trace_cache_repoint_v'+str(i)+'.py'] = text
        text = (HERE/'run_full97_trace_cache_repoint_v1.py').read_text(encoding='utf-8')
        text = text.replace('full97', 'full100').replace('Full97', 'Full100')
        text = text.replace('from full100_consumption_controller import ROOT, ready', 'from full100_consumption_v2_controller import ROOT, ready')
        text = text.replace('full100-trace-cache-repoint-v1', remote)
        text = text.replace('full100_trace_cache_repoint_v1.py', 'full100_trace_cache_repoint_v'+str(i)+'.py')
        files['run_full100_trace_cache_repoint_v'+str(i)+'.py'] = text
    text = (HERE/'full97_trace_recovery_vm_control.py').read_text(encoding='utf-8')
    text = text.replace('full97', 'full100').replace('Full97', 'Full100')
    text = text.replace('from full100_consumption_controller import ROOT,VM,VM_ID,ready', 'from full100_consumption_v2_controller import ROOT,VM,VM_ID,ready')
    text = once(text, 'assert len(executed)==2', 'assert len(executed)==4')
    text = once(text,
        "{'/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v1','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v2'}",
        '{'+','.join(repr('/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v'+str(i)) for i in range(1,5))+'}')
    files['full100_trace_recovery_vm_control.py'] = text
    return files, custody_rows

def main(write=False):
    files, custody = outputs(); rows = []
    for name, text in files.items():
        ast.parse(text); data = text.encode('utf-8'); path = HERE/name
        if write:
            with path.open('xb') as stream: stream.write(data)
        else: assert path.read_bytes() == data
        rows.append(dict(path=name, sha256=digest(path)))
    value = dict(schema='full100-qualified-native-trace-v2-recovery', parent_pins=PINS,
        controls=rows, settled_source_custody=custody, targets_GiB=[s[1] for s in SCOPES],
        current_full100_native_workspace_excluded=True, source_project_objects_and_archives_preserved=True,
        per_file_identity_and_reversibility_and_plan_review_required=True,
        cloud_operation=False, compiler_invoked=False, accepted=False)
    receipt = HERE/'full100-trace-recovery-derivation.json'
    if write:
        with receipt.open('x', encoding='utf-8') as stream: json.dump(value, stream, indent=2); stream.write('\n')
    else: assert json.loads(receipt.read_bytes()) == value
    print('Nine trace recovery controls and four settled-run custody pairs verified; no cloud operation')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
