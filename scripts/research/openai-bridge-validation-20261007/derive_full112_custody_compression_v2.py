"""Retain the first compression and select smaller unchanged committed JSON evidence."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'compress_full112_committed_custody_v1.py'
    text = source.read_text(encoding='utf-8')
    changes = [('path.stat().st_size <= 2_000_000', 'path.stat().st_size <= 250_000'),
               ('reverse=True)[:80]', 'reverse=True)[:120]'),
               ('full112-committed-custody-lossless-v1', 'full112-committed-custody-lossless-v2')]
    for old, new in changes:
        assert text.count(old) == 1
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / 'compress_full112_committed_custody_v2.py'
    target.open('xb').write(text.encode('utf-8'))
    record = dict(parent=source.name, parent_sha256=digest(source), target=target.name,
        target_sha256=digest(target), exact_replacements=changes,
        original_first_result_sha256=digest(HERE / 'full112-committed-custody-lossless-v1/result.json'),
        original_first_execution_preserved=True, inherited_dirt_excluded=True,
        every_original_and_committed_byte_identity_required=True, files_deleted=False)
    (HERE / 'full112-custody-compression-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2) + '\n')


if __name__ == '__main__':
    main()
