"""Freeze separate v2 phase controls without overwriting executed v1 controls."""
from pathlib import Path

def main():
    pairs = [('full89_consumption_worker.py', 'full89_consumption_worker_v2.py'),
             ('full89_consumption_controller.py', 'full89_consumption_controller_v2.py'),
             ('terminate_full89_consumption.py', 'terminate_full89_consumption_v2.py')]
    for old, new in pairs:
        source = Path(__file__).with_name(old).read_text(encoding='utf-8')
        source = source.replace('consumption-v1', 'consumption-v2')
        source = source.replace('full89_consumption_worker.py', 'full89_consumption_worker_v2.py')
        source = source.replace('full89_consumption_controller.py', 'full89_consumption_controller_v2.py')
        if old == 'full89_consumption_controller.py':
            source = source.replace('from custody_checks import digest, verify_local_custody',
                'from custody_checks import digest, verify_local_custody\nfrom prepare_full89_consumption_v2 import validate_predecessor')
            source = source.replace('    full89_controller.validate_successor()',
                '    full89_controller.validate_successor()\n    predecessor_custody = validate_predecessor()')
            source = source.replace("tooling = BASE/'consumption-preparation'", "tooling = BASE/'consumption-preparation-v2-dag'")
            source = source.replace("    readiness = json.loads((tooling/'readiness.json').read_bytes())",
                "    readiness = json.loads((tooling/'readiness.json').read_bytes())\n    if readiness['predecessor_terminal_custody_sha256'] != predecessor_custody['remote_sha256']:\n        raise RuntimeError('Successor is bound to different predecessor evidence')")
            source = source.replace('    custody = verify_local_custody(short, second, pin, size)',
                "    custody = verify_local_custody(short, second, pin, size)\n    custody['vm_retained_for_other_threads'] = False")
        if old == 'terminate_full89_consumption.py':
            source = source.replace('from full89_consumption_controller import', 'from full89_consumption_controller_v2 import')
        with Path(__file__).with_name(new).open('x', encoding='utf-8') as output:
            output.write(source)
    print('Created separate v2 worker, controller and termination controls')

if __name__ == '__main__':
    main()
