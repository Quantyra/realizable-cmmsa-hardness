"""Derive complete Full109 body collection with unchanged custody algorithm."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    parent = (HERE/'prepare_full107_consumption_review_sources.py').read_bytes()
    assert sha(parent) == '424D11ED576E504AFDA85DCDD1C9A3BF01F79AA947B4E84C65361C6A58AFB5AD'
    text = parent.decode('utf-8')
    replacements = [
        ('full107-exact-product-energy-repair-resource02', 'full109-exact-crosslevel-warning-repair-resource02'),
        ('exact260-native', 'exact261-native'),
        ('focused-ninety-two-consumer', 'focused-ninety-three-consumer'),
        ("['roots']) != 92", "['roots']) != 93"),
        ('Complete260/focused92', 'Complete261/focused93'),
        ('Changed Full107 capsule', 'Changed Full109 capsule'),
        ('len(selected) != 346', 'len(selected) != 348'),
        ('full107-complete-captured-project-and-consumption-review-sources-v1', 'full109-complete-captured-project-and-consumption-review-sources-v1'),
        ('selection_complete_for_native260_and_entire_capture', 'selection_complete_for_native261_and_entire_capture'),
        ('All346 complete captured project bodies, exact260 roots/focused-ninety-two', 'All348 complete captured project bodies, exact261 roots/focused-ninety-three'),
    ]
    for old, new in replacements:
        assert text.count(old) == (2 if old == 'exact260-native' else 1)
        text = text.replace(old, new)
    inverse = text
    for old, new in reversed(replacements):
        assert inverse.count(new) == (2 if old == 'exact260-native' else 1)
        inverse = inverse.replace(new, old)
    assert inverse.encode('utf-8') == parent
    ast.parse(text)
    output = text.encode('utf-8')
    target = HERE/'prepare_full109_consumption_review_sources.py'
    with target.open('xb') as stream:
        stream.write(output)
    receipt = dict(parent_sha256=sha(parent), successor_sha256=sha(output), replacements=replacements,
                   exact_inverse_parent_verified=True, source_hash_revision_termination_guards_preserved=True,
                   expected_sources=348, expected_roots=261, expected_focused_roots=93,
                   source_collection_executed=False, compiler_invoked=False, accepted=False)
    with (HERE/'full109-review-source-control-derivation-v1.json').open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2)
        stream.write('\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
