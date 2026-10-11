"""Derive read-only custody of the settled receipt after original SCP failure."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
FAILED = ROOT/'consumption-v3/cache-repoint-controls/20261011T001909531238Z'
WRAPPER = ROOT/'research-resume-20261010/20261011T001754489124Z'


def main():
    commands = json.loads((FAILED/'commands.json').read_bytes())
    assert [c['native_exit'] for c in commands] == [0,0,0,0,1]
    record = json.loads((WRAPPER/'command.json').read_bytes())
    assert record['native_exit'] == 1
    for stream in ('stdout', 'stderr'):
        assert digest(WRAPPER/stream) == record[stream+'_sha256']
    scope = next(s for s in json.loads((HERE/'full109-trace-small-cache-control-derivation-v1.json').read_bytes())['scopes'] if s['number'] == 89)
    assert digest(FAILED/'executed-repoint-control.py') == scope['helper_sha256']
    pin = (FAILED/'control/003.stdout').read_text().split()[0].upper()
    assert pin == '17BDA840557AB015CD086F91E18D68CFB078343779521C57BF2A273F90EA64BA'
    source = HERE/'inspect_full109_trace_recovery_progress_v2.py'
    original = source.read_text(encoding='utf-8')
    text = original
    guard = f'''    failed = Path({str(FAILED)!r})
    wrapper = Path({str(WRAPPER)!r})
    assert json.loads((wrapper/'command.json').read_bytes())['native_exit'] == 1
    assert hashlib.sha256((failed/'commands.json').read_bytes()).hexdigest().upper() == {digest(FAILED/'commands.json')!r}
    assert hashlib.sha256((wrapper/'command.json').read_bytes()).hexdigest().upper() == {digest(WRAPPER/'command.json')!r}
    assert not (ROOT/'consumption-v3/launch-once.json').exists()
'''
    anchor = "    assert SSH.is_file() and KEY.is_file()\n"
    assert text.count(anchor) == 1
    text = text.replace(anchor, anchor+guard)
    text = text.replace("'trace-recovery-progress-v2'", "'readonly-receipt-native89-v1'")
    remote = f'''import base64,hashlib,json,os,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({{}}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={{'Metadata-Flavor':'Google'}})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
root=Path({scope['remote_control']!r})
assert (root/'execute-once.json').is_file()
assert hashlib.sha256((root/{scope['helper']!r}).read_bytes()).hexdigest().upper()=={scope['helper_sha256']!r}
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes()
 except (FileNotFoundError,PermissionError):continue
 assert not (name=='python3' and {scope['helper'].encode()!r} in args), 'Original recovery still live'
data=(root/'receipt.json').read_bytes()
assert hashlib.sha256(data).hexdigest().upper()=={pin!r}
value=json.loads(data);assert len(value['applied'])==19233
print(json.dumps(dict(receipt_sha256={pin!r},raw_receipt_base64=base64.b64encode(data).decode(),read_only=True,execution_replayed=False,compiler_invoked=False)))
'''
    start = text.index('            remote = ')
    end = text.index('            command = ', start)
    text = text[:start]+'            remote = '+repr(remote)+'\n'+text[end:]
    text = text.replace('inspection=result, host_key_fingerprint=fingerprint',
                        'inspection={k:v for k,v in result.items() if k != "raw_receipt_base64"}, host_key_fingerprint=fingerprint')
    ast.parse(text)
    target = HERE/'collect_full109_native89_receipt_v1.py'
    target.open('x', encoding='utf-8', newline='\n').write(text)
    result = dict(parent_sha256=digest(source), successor_sha256=digest(target),
                  original_commands_sha256=digest(FAILED/'commands.json'), original_wrapper_sha256=digest(WRAPPER/'command.json'),
                  original_tool_handle=74386, original_native_exit=1, original_execution_command_native_exit=0,
                  original_failure_reclassified=False, existing_receipt_sha256=pin,
                  fresh_identity_trusted_host_transport_and_local_gates_retained=True,
                  remote_payload_read_only=True, execution_replayed=False, accepted=False)
    (HERE/'full109-native89-receipt-collector-derivation-v1.json').open('x', encoding='utf-8', newline='\n').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
