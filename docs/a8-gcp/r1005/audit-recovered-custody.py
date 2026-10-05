"""Companion custody audit; original runner terminal and legacy audit stay untouched."""
from pathlib import Path
import json, sys
from common import PACKAGE, write_new, json_bytes, file_sha, inherited_now, inherited_status_now

run = PACKAGE / 'runs' / sys.argv[1]
terminal = json.loads((run / 'terminal.json').read_bytes())
custody = json.loads((run / 'bounded-custody.json').read_bytes())
state = json.loads((run / 'custody-stop/terminal.json').read_bytes())
assert state['status'] == 'TERMINATED'
assert custody['before_stop'] and custody['remote_sha256'] == file_sha(run / (run.name + '-evidence.tar.gz'))
original_controls = json.loads((run/'commands.json').read_bytes())
compiler = [row for row in original_controls if any(a.startswith('--command=bash /tmp/') for a in row['argv'])]
assert len(compiler) == 1 and compiler[0]['native_exit'] == 0
controls = list(original_controls)
for row in json.loads((run/'custody-stop/commands.json').read_bytes()):
    row = dict(row)
    row['index'] = len(controls)
    for name in ['stdout_path','stderr_path']:row[name] = 'custody-stop/' + row[name]
    controls.append(row)
write_new(run/'commands-custody-recovered.json',json_bytes(controls))
recovered = dict(terminal)
recovered.update({'failure':None,'vm_terminal_receipt':state,'evidence_archive_sha256':custody['remote_sha256'],
    'custody_recovery':{'original_terminal_sha256':file_sha(run/'terminal.json'),
      'original_runner_failure':terminal['failure'], 'original_runner_legacy_audit_sha256':file_sha(run/'audit.json'),
      'custody_receipt_sha256':file_sha(run/'bounded-custody.json'),
      'note':'Companion summary resolves transport custody only. Original runner failure and raw diagnostics retained. Compiler/source/Checks/axiom stages were not rerun.'}})
write_new(run/'terminal-custody-recovered.json',json_bytes(recovered))
code = (PACKAGE/'audit.py').read_text(encoding='utf-8')
code = code.replace('run / "terminal.json"','run / "terminal-custody-recovered.json"')
code = code.replace('run / "commands.json"','run / "commands-custody-recovered.json"')
write_new(run/'executed-audit-recovered-custody.py',code)
namespace = {'__name__':'custody_audit','__file__':str(run/'executed-audit-recovered-custody.py')}
exec(compile(code,str(run/'executed-audit-recovered-custody.py'),'exec'),namespace)
capture = PACKAGE/'captures'/terminal['capture']
result = namespace['audit_run'](capture,run)
result['custody_recovery'] = recovered['custody_recovery']
write_new(run/'audit-custody-recovered.json',json_bytes(result))
code = (PACKAGE/'prospective-audit.py').read_text(encoding='utf-8')
code = code.replace("run / 'audit.json'", "run / 'audit-custody-recovered.json'")
code = code.replace("run / 'prospective-audit.json'", "run / 'prospective-audit-custody-recovered.json'")
write_new(run/'executed-prospective-audit-custody-recovered.py',code)
namespace = {'__name__':'__main__','__file__':str(run/'executed-prospective-audit-custody-recovered.py')}
exec(compile(code,str(run/'executed-prospective-audit-custody-recovered.py'),'exec'),namespace)
