"""Revalidate immutable Full93 scope and settled parent; never launch."""
import json
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full93 import PARENT, OUTPUT, capsule, parent_custody, validate_expansion


def validate_successor():
    from full92_capture_gates import validate_successor as validate_parent
    validate_parent()
    parent_custody()
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    assert binding['parent_resource_binding_sha256'] == digest(PARENT / 'resource-binding.json')
    assert binding['source_expansion_sha256'] == digest(OUTPUT / 'source-expansion.json')
    for name, pin in binding['files'].items():
        assert digest(OUTPUT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = capsule(OUTPUT / 'input-archive.tar.gz')
    validate_expansion(old, new)
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    assert binding['auxiliary_inputs'] == {n: sha(new[n]) for n in binding['auxiliary_inputs']}
    print(json.dumps({'full93_expansion_verified': True, 'sources': 323, 'profiles': 181,
                      'local_compilation': False, 'launch_clearance': False}))


if __name__ == '__main__':
    validate_successor()
