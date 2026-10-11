"""Retain exact bytes while provisioning reserve from six historical settled traces."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'compress_full109_settled_graphs_v1.py'
    assert digest(source) == '77E721DB54941A6BEB17F6440278E8CA92649393E2C3D43EA9304398DAB7099F'
    scopes = [
        ('full89-resource02', 'consumption-v2', 'qualification'),
        ('full90-material-resource02', 'consumption-v1', 'qualification'),
        ('full95-manuscript-moment-syntax-repair-resource02', 'consumption-v1', 'qualification'),
        ('full97-spectral-bridge-utf8-section-repair-resource02', 'consumption-v1', 'qualification'),
        ('full100-matrix-fourier-bullet-repair-resource02', 'consumption-v2', 'qualification'),
        ('full103-spectral-owned-warning-repair-resource02', 'consumption-v2', 'qualification-v3'),
    ]
    replacements = [
        ("for name in ('full107-exact-product-energy-repair-resource02',\n                 'full109-exact-crosslevel-warning-repair-resource02'):",
         'for name, version, qualification in '+repr(scopes)+':'),
        ("trace = BASE / name / 'consumption-v3'", 'trace = BASE / name / version'),
        ("trace / 'qualification/qualification-summary.json'", "trace / qualification / 'qualification-summary.json'"),
        ("trace / 'qualification' / relative", 'trace / qualification / relative'),
        ('full109-settled-graphs-lossless-compression-v1', 'full109-settled-graphs-lossless-compression-v3'),
        ('full109-settled-graph-lossless-storage-v1', 'full109-settled-graph-lossless-storage-v3')]
    value = source.read_text(encoding='utf-8')
    for old, new in replacements:
        assert value.count(old) == 1
        value = value.replace(old, new)
    ast.parse(value)
    target = HERE / 'compress_full109_settled_graphs_v3.py'
    target.open('xb').write(value.encode('utf-8'))
    record = dict(source=str(source), source_sha256=digest(source), target=str(target),
                  target_sha256=digest(target), replacements=replacements,
                  unchanged_termination_qualification_and_logical_byte_checks=True,
                  no_deletion=True, compiler_invoked=False)
    (HERE / 'full109-storage-reserve-derivation-v3.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(target=str(target), sha256=digest(target), scopes=len(scopes))))


if __name__ == '__main__':
    main()
