"""Recheck exact additive source-size expansion and parent native custody."""
import json
from custody_checks import digest
from prepare_builder02_full91 import PARENT, OUTPUT, CANDIDATES, REQUESTS, capsule, parent_custody, validate_expansion


def validate_successor():
    from full90_capture_gates import validate_successor as validate_parent
    validate_parent()
    parent_custody()
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    assert binding['parent_resource_binding_sha256'] == digest(PARENT / 'resource-binding.json')
    assert binding['source_expansion_sha256'] == digest(OUTPUT / 'source-expansion.json')
    expansion = json.loads((OUTPUT / 'source-expansion.json').read_bytes())
    assert expansion['derivation_sha256'] == digest(CANDIDATES / 'derivation.json')
    assert expansion['additional_profiles'] == binding['additional_profiles'] == REQUESTS
    for name, pin in binding['files'].items():
        assert digest(OUTPUT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = capsule(OUTPUT / 'input-archive.tar.gz')
    changed, added = validate_expansion(old, new, json.loads((CANDIDATES / 'derivation.json').read_bytes()))
    assert changed == binding['changed_files'] and added == binding['added_files']
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    from prepare_builder02 import sha
    assert binding['auxiliary_inputs'] == {n: sha(new[n]) for n in binding['auxiliary_inputs']}
    print(json.dumps({'full91_additive_expansion_verified': True, 'sources': 322,
                      'profiles': 178, 'local_compilation': False, 'launch_clearance': False}))


if __name__ == '__main__':
    validate_successor()
