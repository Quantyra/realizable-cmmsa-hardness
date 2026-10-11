"""Verify exact literal control derivations; never compile or launch cloud work."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'


def main():
    record = json.loads((HERE / 'full116-control-derivation-v1.json').read_bytes())
    for row in record['records']:
        raw = subprocess.check_output(['git', 'cat-file', 'blob', row['source_commit'] + ':' + PREFIX + row['source']], cwd=REPO)
        assert digest(HERE / row['source']) == row['source_sha256']
        import hashlib
        assert hashlib.sha256(raw).hexdigest().upper() == row['source_sha256']
        text = raw.decode().replace('full115', 'full116').replace('Full115', 'Full116')
        text = text.replace('full116-exact-real-complex-operators-repair5', 'full116-exact-real-complex-operators-repair6')
        if row['target'] == 'validate_full116_execution_controls_v1.py':
            text = text.replace('full116-execution-control-derivation-v1.json', 'full116-control-derivation-v1.json')
        expected = text.encode()
        ast.parse(expected, filename=row['target'])
        assert (HERE / row['target']).read_bytes() == expected
        assert digest(HERE / row['target']) == row['target_sha256']
    print(json.dumps(dict(controls=len(record['records']), all_exact_replacements_verified=True,
                         package_prepared=False, compiler_invoked=False, cloud_operation=False)), flush=True)


if __name__ == '__main__':
    main()
