"""Reuse byte-preserving storage checks for three settled Full105 evidence files."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'compress_full109_settled_graphs_v1.py'
    prior = HERE / 'full109-settled-graphs-lossless-compression-v1'
    assert source.read_bytes() == (prior / 'control.snapshot.py').read_bytes()
    assert json.loads((prior / 'result.json').read_bytes())['all_logical_sizes_and_hashes_unchanged']
    replacements = [
        ("('full107-exact-product-energy-repair-resource02',\n                 'full109-exact-crosslevel-warning-repair-resource02')",
         "('full105-actual-consumer-exact-energy-repair-resource02',)"),
        ('full109-settled-graphs-lossless-compression-v1', 'full109-settled-graphs-lossless-compression-v2'),
        ('full109-settled-graph-lossless-storage-v1', 'full109-settled-graph-lossless-storage-v2')]
    text = source.read_text(encoding='utf-8')
    for old, new in replacements:
        assert text.count(old) == 1
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / 'compress_full109_settled_graphs_v2.py'
    target.open('xb').write(text.encode('utf-8'))
    record = dict(source=str(source), source_sha256=digest(source), target=str(target),
                  target_sha256=digest(target), replacements=replacements,
                  unchanged_logical_byte_checks=True, no_deletion=True, compiler_invoked=False)
    (HERE / 'full109-storage-reserve-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
