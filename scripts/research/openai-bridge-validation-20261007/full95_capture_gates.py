"""Exact immutable syntax-only successor scope; no launch or compilation."""
import json
from custody_checks import digest
from prepare_builder02_full95 import PARENT, OUTPUT, capsule, parent_custody, validate_repair


def validate_successor():
    from full94_capture_gates import validate_successor as validate_parent
    validate_parent()
    parent_custody()
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    assert binding['parent_resource_binding_sha256'] == digest(PARENT / 'resource-binding.json')
    assert binding['source_expansion_sha256'] == digest(OUTPUT / 'source-expansion.json')
    for name, pin in binding['files'].items():
        assert digest(OUTPUT / name) == pin
    old, new = capsule(PARENT / 'input-archive.tar.gz'), capsule(OUTPUT / 'input-archive.tar.gz')
    validate_repair(old, new)
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    parent_binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    assert binding['auxiliary_inputs'] == parent_binding['auxiliary_inputs']
    assert binding['additional_profiles'] == parent_binding['additional_profiles']
    print(json.dumps({'full95_syntax_only_repair_verified': True, 'sources': 323,
                      'profiles': 181, 'local_compilation': False, 'launch_clearance': False}))


if __name__ == '__main__':
    validate_successor()
