"""Verify immutable full346/full260 successor; no Lean/cloud execution."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full106 import OUTPUT
from prepare_full106_product_energy_scope import PARENT, validate_expansion


def validate_successor():
    from full105_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT/name) == pin
    assert digest(PARENT/'resource-binding.json') == binding['parent_resource_binding_sha256']
    assert digest(OUTPUT/'source-expansion.json') == binding['source_expansion_sha256']
    new = capsule(OUTPUT/'input-archive.tar.gz')
    assert new['capture-manifest.json'] == (OUTPUT/'capture-manifest.json').read_bytes()
    validate_expansion(capsule(PARENT/'input-archive.tar.gz'), new)
    print('Full106 preserves full344 parent, adds two sources/three profiles; full346/full260/seven stages')


if __name__ == '__main__':
    validate_successor()
