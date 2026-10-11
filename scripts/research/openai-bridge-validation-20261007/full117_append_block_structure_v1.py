"""Preserve the exact 18 declarations, disclosing one explicit alias qualification."""
import re
from full114_gl_repair_structure_v1 import declarations

QUALIFIED = 'ExactAppendOperatorContracts.FullRowFrame'
QUALIFIED_HEADER = 'last_rows_inverse_uniform_mean'


def validate(old, new):
    before, after = declarations(old), declarations(new)
    assert len(before) == 18 and list(before) == list(after)
    changed = []
    for name, row in before.items():
        current = after[name].copy()
        if name == QUALIFIED_HEADER:
            current['header'] = current['header'].replace(QUALIFIED, 'FullRowFrame')
        assert current == row, ('Existing declaration changed', name)
        if after[name] != row:
            changed.append(name)
    assert changed == [QUALIFIED_HEADER]
    assert new.decode().count(QUALIFIED) == 10
    assert re.findall(rb'^import .+$', old, re.M) == re.findall(rb'^import .+$', new, re.M)
    assert re.findall(rb'^set_option .+$', old, re.M) == re.findall(rb'^set_option .+$', new, re.M)
    return dict(declarations=18, explicitly_qualified_public_header=QUALIFIED_HEADER,
                literal_header_bytes_unchanged=False, remaining_headers_exact=True,
                source_qualified_alias_occurrences=10, imports_options_unchanged=True,
                heartbeat_default_preserved=True)
