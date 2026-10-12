"""Verify the exact one-source rank Gram proof repair with exact existing headers against every unchanged Full118 capture member."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full119 import OUTPUT, PARENT, validate_expansion


def validate_successor():
    from full118_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT / name) == pin
    assert digest(PARENT / 'resource-binding.json') == binding['parent_resource_binding_sha256']
    assert digest(OUTPUT / 'source-expansion.json') == binding['source_expansion_sha256']
    new = capsule(OUTPUT / 'input-archive.tar.gz')
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    validate_expansion(capsule(PARENT / 'input-archive.tar.gz'), new)
    print('Full119 exact one-source rank Gram proof repair with exact existing headers preserves full369/full347/seven-stage scope')


if __name__ == '__main__':
    validate_successor()
