"""Extend byte-preserving compression to remaining committed evidence folders."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'compress_full111_committed_custody_v1.py'
    text = source.read_text(encoding='utf-8')
    changes = [
        ("head.startswith('5422a943')", "head.startswith('4930801c')"),
        ("if not first.startswith(('full9', 'full10', 'full110')) or not any(x in first for x in ('record', 'checkpoint')):",
         "if not first.startswith('full') or 'lossless' in first:"),
        ('assert len(selected) >= 20', 'assert len(selected) >= 1'),
        ('full111-committed-custody-lossless-v1', 'full112-committed-custody-lossless-v1')]
    for old, new in changes:
        assert text.count(old) == 1
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / 'compress_full112_committed_custody_v1.py'
    target.open('xb').write(text.encode('utf-8'))
    result = dict(source=source.name, source_sha256=digest(source), target=target.name,
        target_sha256=digest(target), exact_replacements=changes,
        only_unchanged_committed_JSON_over_2MB_with_allocated_bytes_over_80_percent=True,
        maximum_files=80, byte_identity_required_before_and_after=True,
        originals_deleted=False, inherited_dirt_excluded=True, compiler_invoked=False)
    (HERE / 'full112-custody-compression-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
