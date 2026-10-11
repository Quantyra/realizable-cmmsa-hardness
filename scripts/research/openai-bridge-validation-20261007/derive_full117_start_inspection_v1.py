"""Prepare a disjoint owned start/read-only capacity controller; no cloud action."""
import ast
from pathlib import Path
H = Path(__file__).resolve().parent

def main():
    text = (H / 'stage_full116_openssh_v1.py').read_text()
    text = text[:text.index('    time.sleep(30)')]
    text = text.replace('full116', 'full117').replace('Full116', 'Full117')
    replacements = {
        'full115-exact-real-complex-operators-repair5-resource02': 'full116-exact-real-complex-operators-repair6-resource02',
        '20261011T201255199859Z': '20261011T212845260237Z',
        '9495001F3BA6C4194E4DB4BB8563BE399E48FD8D7CDED513395EEF16021C612A': 'D6903AB914994BDB6B7C7750D8956C06611CBFE7ACDAEA8E96058DD2F1B1EB2C',
        'full115-native-final-custody-v1': 'full116-native-final-custody-v1',
        '8BB7BD5C36A62CBBC0CE1C96787EDF487B53276F78D775BC1E8D34B142344B1D': '7C3B8FC2E4F2CC8D42295712BCE8968B54606C452A867BE05F75EB438B1B5519',
        'cmmsa_a8_output_20261011T201326Z_31fcd86a': 'cmmsa_a8_output_20261011T212933Z_f9a386c2',
    }
    for old, new in replacements.items():
        assert old in text
        text = text.replace(old, new)
    text = text.replace('    validate_successor();', '    verify_cleanup_receipt()\n    validate_successor();')
    text += (H / 'full117_start_inspection_tail_v1.txt').read_text()
    ast.parse(text)
    (H / 'start_inspect_full117_owned_capacity_v1.py').open('x', encoding='utf-8').write(text)

if __name__ == '__main__':
    main()
