"""Offline receipt-gate negatives on disjoint scratch copies; no cloud action."""
import json
from pathlib import Path
from unittest.mock import patch
import start_inspect_full117_owned_capacity_v2 as controller

H = Path(__file__).resolve().parent

def main():
    original = H / 'full117-approved20-extracted-cleanup-receipt-v1'
    scratch = H / 'full117-cleanup-receipt-gate-tests-v2'
    scratch.mkdir(exist_ok=False)
    (scratch / '.gitattributes').write_bytes(b'* -text\n')
    results = []
    for name in ('positive', 'changed_receipt_bytes', 'missing_receipt', 'wrong_authorization'):
        root = scratch / name
        folder = root / original.name
        folder.mkdir(parents=True)
        if name != 'missing_receipt':
            (folder / 'receipt.json').write_bytes((original / 'receipt.json').read_bytes())
            (folder / 'authorization.json').write_bytes((original / 'authorization.json').read_bytes())
        if name == 'changed_receipt_bytes':
            with (folder / 'receipt.json').open('ab') as stream:
                stream.write(b' ')
        if name == 'wrong_authorization':
            value = json.loads((folder / 'authorization.json').read_bytes())
            value['actual_reply'] = 'Not approved'
            (folder / 'authorization.json').write_text(json.dumps(value) + '\n', encoding='utf-8')
        rejected = False
        with patch.object(controller, '__file__', str(root / 'controller.py')):
            try:
                controller.verify_cleanup_receipt()
            except (AssertionError, FileNotFoundError):
                rejected = True
        assert rejected == (name != 'positive'), name
        results.append(dict(test=name, rejected=rejected))
    (scratch / 'result.json').write_text(json.dumps(dict(tests=results, compiler_invoked=False,
        cloud_operation=False, failed_initial_test_chunk='81957f',
        initial_failure='Mocked Path.read_bytes did not mock streaming digest; test harness failed without changing real receipts'),
        indent=2) + '\n', encoding='utf-8')
    print(json.dumps(results), flush=True)

if __name__ == '__main__':
    main()
