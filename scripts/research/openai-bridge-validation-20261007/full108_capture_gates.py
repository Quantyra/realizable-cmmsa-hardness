"""Verify complete immutable Full108 additive capture; no launch clearance."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full108 import OUTPUT, PARENT
from prepare_full108_crosslevel_product_scope import HERE, validate_expansion


def validate_successor():
    from full107_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding = json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(OUTPUT/name) == pin
    assert digest(PARENT/'resource-binding.json') == binding['parent_resource_binding_sha256']
    assert digest(OUTPUT/'source-expansion.json') == binding['source_expansion_sha256']
    expansion = json.loads((OUTPUT/'source-expansion.json').read_bytes())
    assert expansion['parent_qualified_green']
    assert expansion['parent_qualified_report_sha256'] == 'C787891955E5688EAC6820643FD26D61755F955D8AED53DE95893801CAE29765'
    assert digest(HERE/'full108-crosslevel-product-scope-proposal-v1.json') == expansion['scope_proposal_sha256']
    assert expansion['all346_parent_source_bytes_and260_profiles_preserved']
    assert expansion['all_seven_parent_stage_prefixes_preserved']
    assert not expansion['compiler_invoked'] and not expansion['launch_clearance']
    new = capsule(OUTPUT/'input-archive.tar.gz')
    assert new['capture-manifest.json'] == (OUTPUT/'capture-manifest.json').read_bytes()
    validate_expansion(capsule(PARENT/'input-archive.tar.gz'), new)
    for name, pin in binding['auxiliary_inputs'].items():
        from prepare_builder02 import sha
        assert sha(new[name]) == pin
    print('Full108 preserves all346 parent sources/full260 profiles, adds two sources/one profile; full348/full261/seven stages')


if __name__ == '__main__':
    validate_successor()
