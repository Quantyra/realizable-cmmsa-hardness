"""Verify immutable full-scope one-file successor without Lean or cloud."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full105 import OUTPUT, PARENT, REPAIRS, validate_expansion


def validate_successor():
    from full104_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT/name) == pin
    assert digest(PARENT/'resource-binding.json') == binding['parent_resource_binding_sha256']
    assert digest(OUTPUT/'source-expansion.json') == binding['source_expansion_sha256']
    expansion = json.loads((OUTPUT/'source-expansion.json').read_bytes())
    assert digest(REPAIRS/'derivation.json') == expansion['repair_derivation_sha256']
    new = capsule(OUTPUT/'input-archive.tar.gz')
    assert new['capture-manifest.json'] == (OUTPUT/'capture-manifest.json').read_bytes()
    validate_expansion(capsule(PARENT/'input-archive.tar.gz'), new)
    print('Full105 one-proof repair preserves full344/full257/seven-stage scope')


if __name__ == '__main__':
    validate_successor()
