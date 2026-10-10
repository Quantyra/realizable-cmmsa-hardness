"""Verify exact parent-control derivation for the unchanged Full107 scope."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent


def main():
    record = json.loads((HERE/'full107-execution-control-derivation.json').read_bytes())
    assert (record['sources'], record['profiles'], record['stages']) == (346, 260, 7)
    assert len(record['records']) == 7
    for row in record['records']:
        raw = (HERE/row['source']).read_bytes()
        assert hashlib.sha256(raw).hexdigest().upper() == row['source_sha256']
        text = raw.decode().replace('full106-exact-product-energy', 'full107-exact-product-energy-repair')
        text = text.replace('full106', 'full107').replace('Full106', 'Full107')
        if row['source'] == 'full106_builder02_controller.py':
            text = text.replace("'prepare_full107_product_energy_scope.py','test_full107_scope.py'",
                                "'prepare_full106_product_energy_scope.py','test_full106_scope.py','test_full107_capture_gates.py'")
        ast.parse(text)
        target = (HERE/row['target']).read_bytes()
        assert target == text.encode()
        assert hashlib.sha256(target).hexdigest().upper() == row['target_sha256']
    print('Seven exact parent-control derivations verified; full346/full260/seven stages')


if __name__ == '__main__':
    main()
