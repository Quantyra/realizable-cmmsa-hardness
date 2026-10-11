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
    record = json.loads((HERE / 'full118-control-derivation-v1.json').read_bytes())
    for row in record['records']:
        raw = subprocess.check_output(['git', 'cat-file', 'blob', row['source_commit'] + ':' + PREFIX + row['source']], cwd=REPO)
        assert digest(HERE / row['source']) == row['source_sha256']
        import hashlib
        assert hashlib.sha256(raw).hexdigest().upper() == row['source_sha256']
        text = raw.decode().replace('full117','full118').replace('Full117','Full118').replace('repair7','repair8')
        if row['target']=='validate_full118_execution_controls_v1.py':
            text=text.replace('full118_append_block_structure_v1.py','full118_restricted_adjoint_structure_v3.py')
        expected = text.encode()
        ast.parse(expected, filename=row['target'])
        assert (HERE / row['target']).read_bytes() == expected
        assert digest(HERE / row['target']) == row['target_sha256']
    print(json.dumps(dict(controls=len(record['records']), all_exact_replacements_verified=True,
                         package_prepared=False, compiler_invoked=False, cloud_operation=False)), flush=True)


if __name__ == '__main__':
    main()
