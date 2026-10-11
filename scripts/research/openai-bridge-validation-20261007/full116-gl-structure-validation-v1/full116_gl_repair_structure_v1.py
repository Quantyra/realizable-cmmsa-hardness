"""Preserve all selected-row declarations and permit exactly two private helpers."""
import re
from full114_gl_repair_structure_v1 import declarations

HELPERS = {'selectedMap_fiber_equiv': 'private noncomputable def',
           'selectedMap_fiber_card_eq': 'private theorem'}


def validate(old, new):
    before, after = declarations(old), declarations(new)
    assert set(after) - set(before) == set(HELPERS)
    assert set(before) <= set(after)
    assert all(after[name] == row for name, row in before.items())
    assert list(before) == [name for name in after if name not in HELPERS]
    assert all(after[name]['kind'] == kind for name, kind in HELPERS.items())
    for pattern in (r'(?m)^import .+$', r'(?m)^set_option .+$'):
        assert re.findall(pattern, old.decode()) == re.findall(pattern, new.decode())
    assert not re.findall(r'(?m)^set_option maxHeartbeats\b', new.decode())
    return dict(existing_headers_preserved=len(before), private_helpers=HELPERS,
                imports_and_options_preserved=True, default_heartbeat_cap_unchanged=200000)
