"""Preserve every declaration and option across the cardinal-instance repair."""
import re
from full114_gl_repair_structure_v1 import declarations


def validate(old, new):
    before, after = declarations(old), declarations(new)
    assert before == after, 'Declaration, order, or header changed'
    for pattern in (r'(?m)^import .+$', r'(?m)^set_option .+$'):
        assert re.findall(pattern, old.decode('utf-8')) == re.findall(pattern, new.decode('utf-8'))
    assert re.findall(r'(?m)^set_option maxHeartbeats (\d+) in$', new.decode('utf-8')) == ['400000']
    assert b'hcardNat' in new and b'hcardExpected' not in new
    return dict(existing_declarations_preserved=len(before), no_added_declarations=True,
                imports_and_options_preserved=True, heartbeat_cap=400000)
