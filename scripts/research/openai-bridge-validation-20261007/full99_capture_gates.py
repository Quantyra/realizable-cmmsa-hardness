"""Exact additive Full98 gates; no compiler or VM operation."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full99 import OUTPUT, PARENT, CANDIDATES, validate_expansion


def validate_successor():
    from full98_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT / name) == pin
    expansion = json.loads((OUTPUT / 'source-expansion.json').read_bytes())
    assert digest(OUTPUT / 'source-expansion.json') == binding['source_expansion_sha256']
    assert digest(CANDIDATES / 'derivation.json') == expansion['candidate_derivation_sha256']
    assert digest(PARENT / 'resource-binding.json') == binding['parent_resource_binding_sha256']
    new = capsule(OUTPUT / 'input-archive.tar.gz')
    validate_expansion(capsule(PARENT / 'input-archive.tar.gz'), new)
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    print(json.dumps(dict(full99_full327_full192_syntax_only_scope_verified=True,
                         local_compilation=False, launch_clearance=False)))


if __name__ == '__main__':
    validate_successor()
