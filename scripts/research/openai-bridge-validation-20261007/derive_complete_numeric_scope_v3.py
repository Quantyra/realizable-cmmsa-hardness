"""Extend the static Full114 proposal with the two captured compositions."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'prepare_complete_numeric_scope_v2.py'
    original = source.read_bytes()
    assert sha(original) == 'CB7F6DDF6700A34BF2B716D0F0DC4EB4E160A33FAD9FC38F16C28BC19D8D9634'
    raw = original.decode('utf-8')
    anchor = "    ('numeric-exact-threshold-capture-v2', 'EFEC33817B3F7585E51AD5DA03840F8566E7C3FF61DA5FE8F0E30C3A21C62C22'),"
    replacement = anchor + "\n    ('numeric-same-instance-composition-capture-v2', '48672D236093387B5D9E8C8AFF076F490EB9783A740B63761E804323974CA46D'),\n    ('numeric-physical-density-capture-v2', '6D95E2F441AB49926E359E8C444245915B738DAAB77FB1C2ABBBB1469B50C087'),"
    replacements = [
        ('the six captured numeric and density offers', 'the eight captured numeric, density and composition offers'),
        (anchor, replacement),
        ('assert len(sources) == 12', 'assert len(sources) == 16'),
        ('len(requests) == 31', 'len(requests) == 34'),
        ('== 381', '== 385'), ('== 378', '== 381'),
        ('sources=381', 'sources=385'), ('profiles=378', 'profiles=381'),
        ('complete-numeric-additive-scope-proposal-v2', 'complete-numeric-additive-scope-proposal-v3'),
        ('Full114 native verification in progress; no acceptance asserted',
         'Full114 failed with one GL source error; independently stopped; unchanged audit failed; not accepted'),
        ('Join exact rational maximum, scalar contradiction and same selected numeric floor',
         'GCP-verify the complete same-instance Real inverse composition and physical-density consequence'),
        ('Route original global acceptance to the same-instance side density; source/table/sampler obligations remain under audit',
         'Manuscript-to-physical score transport, positive-mass robust-source overlap and SAT-derived source NO promise; no favorable table witness required'),
    ]
    rows = []
    for old, new in replacements:
        count = raw.count(old)
        assert count > 0, old
        raw = raw.replace(old, new)
        rows.append(dict(before=old, after=new, count=count))
    ast.parse(raw)
    reconstructed = raw
    for row in reversed(rows):
        assert reconstructed.count(row['after']) == row['count'], row
        reconstructed = reconstructed.replace(row['after'], row['before'])
    assert reconstructed == original.decode('utf-8')
    target = HERE / 'prepare_complete_numeric_scope_v3.py'
    target.open('x', encoding='utf-8', newline='\n').write(raw)
    result = dict(parent_control_sha256=sha(original), successor_control_sha256=sha(target.read_bytes()),
        replacements=rows, inverse_reconstruction_exact=True,
        eight_immutable_captures=True, parent_sources_retained=369, parent_requests_retained=347,
        original_seven_stage_prefixes_and_ten_negative_tests_retained=True,
        mathematical_sources_edited=False, execution_archive_created=False, compiler_invoked=False)
    (HERE / 'complete-numeric-scope-derivation-v3.json').open('x', encoding='utf-8', newline='\n').write(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(control=target.name, sha256=result['successor_control_sha256'],
                         inverse_reconstruction_exact=True)))


if __name__ == '__main__':
    main()
