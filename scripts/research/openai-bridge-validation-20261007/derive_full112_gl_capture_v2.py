"""Capture the separate definitional transpose repair; retain v1 unchanged."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'capture_full112_rectangular_gl_repair_v1.py'
    text = source.read_text(encoding='utf-8')
    changes = [
        ('full112-rectangular-gl-repair-v1', 'full112-rectangular-gl-repair-v2'),
        ('81F5FA274FAA21B6DA42E06E7208C6BC9998FBDB2D0DB2A7956D6DE1FC7B3124', 'E56B4BA7A035AFA019495E3F4342B27A4F53B5489CAEF9C33A4DBAAEE525B1AE'),
        ('full112-rectangular-gl-repair-capture-v1', 'full112-rectangular-gl-repair-capture-v2'),
        ("root_read_complete_diff_and_argument_map=True,", "root_read_complete_diff_and_argument_map=True, preserved_stale_manifest_offer_label='full112-rectangular-gl-repair-v1',")]
    for old, new in changes:
        assert text.count(old) == 1
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / 'capture_full112_rectangular_gl_repair_v2.py'
    target.open('xb').write(text.encode('utf-8'))
    record = dict(parent=source.name, parent_sha256=digest(source), target=target.name,
        target_sha256=digest(target), exact_replacements=changes,
        parent_capture_index_sha256=digest(HERE / 'full112-rectangular-gl-repair-capture-v1/index.json'),
        rationale='Use only definitional toLin/mulVec coercions; avoid unnecessary simp rewrites.',
        compiler_invoked=False)
    (HERE / 'full112-gl-capture-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2) + '\n')


if __name__ == '__main__':
    main()
