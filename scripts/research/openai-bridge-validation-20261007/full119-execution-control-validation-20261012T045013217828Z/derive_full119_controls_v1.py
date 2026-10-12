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
    record = json.loads((HERE / 'full119-control-derivation-v1.json').read_bytes())
    for row in record['records']:
        raw = subprocess.check_output(['git', 'cat-file', 'blob', row['source_commit'] + ':' + PREFIX + row['source']], cwd=REPO)
        assert digest(HERE / row['source']) == row['source_sha256']
        import hashlib
        assert hashlib.sha256(raw).hexdigest().upper() == row['source_sha256']
        text = raw.decode().replace('full118','full119').replace('Full118','Full119').replace('repair8','repair9')
        if row['target']=='validate_full119_execution_controls_v1.py':
            text=text.replace('full119_restricted_adjoint_structure_v3.py','full119_rank_gram_structure_v1.py')
        expected = text.encode()
        ast.parse(expected, filename=row['target'])
        assert (HERE / row['target']).read_bytes() == expected
        assert digest(HERE / row['target']) == row['target_sha256']
    print(json.dumps(dict(controls=len(record['records']), all_exact_replacements_verified=True,
                         package_prepared=False, compiler_invoked=False, cloud_operation=False)), flush=True)


if __name__ == '__main__':
    main()
