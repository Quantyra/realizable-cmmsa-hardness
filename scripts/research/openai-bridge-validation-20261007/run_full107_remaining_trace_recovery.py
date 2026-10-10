"""Run only the five remaining reviewed recoveries, sequentially and once."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
from audit_full107_trace_cache_recovery_v1_v4_v8 import ROOT, plan_review, receipt_review
from custody_checks import digest

HERE = Path(__file__).parent
REVIEW_SHA = '14532AA9BF8EC20D6CF1B90934FDF481EB3B90B35AD8B310419F6C03E48A813D'


def main():
    assert not (ROOT/'launch-once.json').exists(), 'Trace already launched'
    plan_review()
    assert digest(ROOT/'complete-trace-cache-plan-review-v1-v4-v8.json') == REVIEW_SHA
    receipt_review(1)
    for number in (4, 5, 6, 7, 8):
        remote = '/home/dfredriksen_quantyra_org/full107-trace-cache-repoint-v'+str(number)
        for path in (ROOT/'cache-repoint-controls').glob('*/operation.json'):
            op = json.loads(path.read_bytes())
            assert not (op['remote_control'] == remote and op['action'] == 'execute'), 'Existing transaction; inspect it'
    folder = ROOT/'remaining-recovery-batch'
    folder.mkdir()
    (folder/'batch-once.json').open('x').write(json.dumps(dict(review_sha256=REVIEW_SHA, scopes=[4,5,6,7,8], utc=datetime.now(timezone.utc).isoformat()))+'\n')
    terminal = dict(completed_scopes=[], failure=None, probe_invoked=False, VM_power_operation=False)
    try:
        for number in (4, 5, 6, 7, 8):
            assert not (ROOT/'launch-once.json').exists()
            command = [sys.executable, '-B', '-X', 'utf8', str(HERE/f'run_full107_trace_cache_repoint_v{number}.py'), 'execute']
            (folder/f'scope{number}.command.json').write_text(json.dumps(command)+'\n')
            with (folder/f'scope{number}.stdout').open('xb') as out, (folder/f'scope{number}.stderr').open('xb') as err:
                code = subprocess.run(command, stdout=out, stderr=err).returncode
            (folder/f'scope{number}.native-exit.json').write_text(json.dumps(dict(native_exit=code))+'\n')
            if code:
                raise RuntimeError(f'Scope{number} failed with native exit{code}; retain original receipts')
            receipt_review(number)
            terminal['completed_scopes'].append(number)
            print(json.dumps(dict(scope=number, native_exit=0, complete_receipt_audited=True)), flush=True)
    except BaseException as error:
        terminal['failure'] = str(error)
        raise
    finally:
        (folder/'batch-terminal.json').open('x').write(json.dumps(terminal, indent=2)+'\n')


if __name__ == '__main__':
    assert not sys.argv[1:]
    main()
