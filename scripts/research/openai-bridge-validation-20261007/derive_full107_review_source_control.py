"""Derive complete Full107 source collection without executing collection."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent
PARENT_SHA = '39775452BF0E29DE1C49DBB52674DBEA023C002844FB4D5A270EC664083962A9'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    parent = (HERE/'prepare_full105_consumption_review_sources.py').read_bytes()
    assert sha(parent) == PARENT_SHA, 'Parent source collection control drift'
    text = parent.decode('utf-8')
    replacements = [
        ('full105-actual-consumer-exact-energy-repair-resource02', 'full107-exact-product-energy-repair-resource02'),
        ('exact257-native', 'exact260-native'),
        ('focused-eighty-nine-consumer', 'focused-ninety-two-consumer'),
        ("['roots']) != 89", "['roots']) != 92"),
        ('Complete257/focused89', 'Complete260/focused92'),
        ('Changed Full105 capsule', 'Changed Full107 capsule'),
        ('len(selected) != 344', 'len(selected) != 346'),
        ('full105-complete-captured-project-and-consumption-review-sources-v1', 'full107-complete-captured-project-and-consumption-review-sources-v1'),
        ('selection_complete_for_native257_and_entire_capture', 'selection_complete_for_native260_and_entire_capture'),
        ('All344 complete captured project bodies, exact257 roots/focused-eighty-nine', 'All346 complete captured project bodies, exact260 roots/focused-ninety-two'),
    ]
    counts = {'exact257-native': 2}
    for old, new in replacements:
        assert text.count(old) == counts.get(old, 1), (old, text.count(old))
        text = text.replace(old, new)
    inverse = text
    for old, new in reversed(replacements):
        assert inverse.count(new) == counts.get(old, 1), (new, inverse.count(new))
        inverse = inverse.replace(new, old)
    assert inverse.encode('utf-8') == parent, 'Non-scope algorithm change'
    ast.parse(text)
    output = text.encode('utf-8')
    target = HERE/'prepare_full107_consumption_review_sources.py'
    if target.exists():
        assert target.read_bytes() == output, 'Existing successor drift'
    else:
        target.open('xb').write(output)
    receipt = dict(schema='full107-complete346-body-source-control-derivation-v1',
                   parent_sha256=sha(parent), successor_sha256=sha(output),
                   replacements=replacements, exact_inverse_parent_verified=True,
                   archive_source_hash_revision_termination_guards_preserved=True,
                   compiler_invoked=False, source_collection_executed=False,
                   accepted=False)
    data = (json.dumps(receipt, indent=2)+'\n').encode('utf-8')
    path = HERE/'full107-review-source-control-derivation-v1.json'
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
