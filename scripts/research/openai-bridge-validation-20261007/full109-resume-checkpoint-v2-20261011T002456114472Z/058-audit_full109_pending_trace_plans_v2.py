"""Revalidate the six inherited plans and their exact preservation records."""
import json
from pathlib import Path
from audit_full109_trace_cache_small_v1 import main as audit
from custody_checks import digest
from full109_builder02_controller import ROOT


def main():
    here = Path(__file__).parent
    auditor = here/'audit_full109_trace_cache_small_v1.py'
    initial = digest(auditor)
    scopes = []
    for number in range(84, 90):
        audit('plan', number)
        preserved = here/f'full109-trace-small-plan-native{number}-record-v1'
        index = json.loads((preserved/'index.json').read_bytes())
        assert index['native_exit'] == 0 and index['complete_current_row_audit']
        for row in index['records']:
            original, copy = Path(row['source']), preserved/row['target']
            assert original.stat().st_size == copy.stat().st_size == row['bytes']
            assert digest(original) == digest(copy) == row['sha256']
        current = ROOT/'consumption-v3'/f'cache-small-plan-audit-native{number}-v1.json'
        record = json.loads(current.read_bytes())
        scopes.append(dict(number=number, audit_sha256=digest(current), rows=record['rows'],
                           plan_sha256=record['plan_sha256'], preservation_files=len(index['records'])))
    assert digest(auditor) == initial
    target = ROOT/'consumption-v3/pending-plans-revalidation-v2.json'
    result = dict(scopes=scopes, auditor_sha256=initial, all_original_and_preserved_bytes_verified=True,
                  recovery_executed=False, trace_executed=False, accepted=False)
    with target.open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
