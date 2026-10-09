"""Exact immutable warning-only successor gate; never launch a compiler."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full102 import OUTPUT,PARENT,REPAIRS,validate_expansion


def validate_successor():
    from full101_capture_gates import validate_successor as parent_gate
    parent_gate()
    b=json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name,pin in b['files'].items():assert digest(OUTPUT/name)==pin
    assert digest(PARENT/'resource-binding.json')==b['parent_resource_binding_sha256']
    assert digest(OUTPUT/'source-expansion.json')==b['source_expansion_sha256']
    e=json.loads((OUTPUT/'source-expansion.json').read_bytes())
    assert digest(REPAIRS/'derivation.json')==e['repair_derivation_sha256']
    new=capsule(OUTPUT/'input-archive.tar.gz')
    assert new['capture-manifest.json']==(OUTPUT/'capture-manifest.json').read_bytes()
    validate_expansion(capsule(PARENT/'input-archive.tar.gz'),new)
    print('Full102 exact eight-proof repair preserves full340/full251/seven-stage capture')


if __name__=='__main__':validate_successor()
