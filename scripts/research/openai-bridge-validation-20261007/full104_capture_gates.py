"""Validate frozen actual-consumer/energy expansion without Lean or cloud."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full104 import OUTPUT
from prepare_full104_consumer_energy_scope import PARENT, HERE, make_successor, validate_expansion


def validate_successor():
    from full103_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT/name) == pin
    assert digest(PARENT/'resource-binding.json') == binding['parent_resource_binding_sha256']
    assert digest(OUTPUT/'source-expansion.json') == binding['source_expansion_sha256']
    expansion = json.loads((OUTPUT/'source-expansion.json').read_bytes())
    assert digest(HERE/'full104-consumer-energy-scope-proposal-v1.json') == expansion['scope_proposal_sha256']
    assert digest(HERE/'full104-static-candidate-review-reuse-v1.json') == expansion['prior_static_candidate_review_reuse_sha256']
    old = capsule(PARENT/'input-archive.tar.gz')
    new = capsule(OUTPUT/'input-archive.tar.gz')
    assert new == make_successor(old)
    assert new['capture-manifest.json'] == (OUTPUT/'capture-manifest.json').read_bytes()
    validate_expansion(old, new)
    for name, pin in binding['auxiliary_inputs'].items():
        from prepare_builder02 import sha
        assert sha(new[name]) == pin
    print('Full104 exact consumer/energy expansion preserves full344/full257/seven-stage capture')


if __name__ == '__main__':
    validate_successor()
