"""Check existing declarations exactly, allowing only two reviewed private GL helpers."""
import re
from lean_source_static_preflight_v1 import code_only

HELPERS = {'rowPrefix_fiber_equiv': 'private noncomputable def',
           'rowPrefix_fiber_card_eq': 'private theorem'}


def declarations(data):
    text = code_only(data.decode('utf-8'))
    starts = list(re.finditer(r'(?m)^(?P<kind>(?:(?:private|noncomputable|protected) )*'
                             r'(?:theorem|lemma|def|abbrev|instance))\s+(?P<name>\w+)', text))
    rows = {}
    for i, match in enumerate(starts):
        end = starts[i+1].start() if i+1 < len(starts) else len(text)
        chunk = text[match.start():end]
        delimiter = re.search(r':=|\bwhere\b', chunk)
        assert delimiter, 'Missing declaration boundary: ' + match['name']
        assert match['name'] not in rows
        rows[match['name']] = dict(kind=match['kind'], header=chunk[:delimiter.start()].rstrip())
    assert rows
    return rows


def validate(old, new):
    a, b = declarations(old), declarations(new)
    assert set(b) - set(a) == set(HELPERS)
    assert set(a) <= set(b)
    assert all(b[name] == row for name, row in a.items()), 'Existing declaration changed'
    assert all(b[name]['kind'] == kind for name, kind in HELPERS.items())
    assert list(a) == [name for name in b if name not in HELPERS]
    assert re.findall(r'(?m)^import .+$', old.decode()) == re.findall(r'(?m)^import .+$', new.decode())
    assert re.findall(r'(?m)^set_option maxHeartbeats (\d+) in$', old.decode()) == ['800000']
    assert re.findall(r'(?m)^set_option maxHeartbeats (\d+) in$', new.decode()) == ['400000']
    return dict(existing_declarations_preserved=len(a),
                added_private_helpers={name:b[name] for name in HELPERS},
                old_header_parser_not_used='Recognize both := and where; do not absorb following declarations into a where-definition header.')
