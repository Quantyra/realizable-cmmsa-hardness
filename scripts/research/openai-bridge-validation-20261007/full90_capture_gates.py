"""Validate full repair provenance and the exact added material export/profile."""
import json
from full89_controller import validate_successor as validate_parent
from prepare_builder02_full90 import PARENT, OUTPUT, REL, REQUEST, CANDIDATE_SHA, capsule, validate_expansion, parent_custody
from custody_checks import digest


def validate_successor():
    validate_parent()
    parent_custody()
    binding = json.loads((OUTPUT/'resource-binding.json').read_bytes())
    expansion = json.loads((OUTPUT/'source-expansion.json').read_bytes())
    if binding['parent_resource_binding_sha256'] != digest(PARENT/'resource-binding.json') or binding['source_expansion_sha256'] != digest(OUTPUT/'source-expansion.json'):
        raise RuntimeError('Parent/source expansion binding drift')
    if expansion['source'] != REL or expansion['new_sha256'] != CANDIDATE_SHA or expansion['additional_profile'] != REQUEST:
        raise RuntimeError('Material expansion identity drift')
    if not all(expansion[name] for name in ['original172_requests_preserved','all_seven_stages_preserved','other318_sources_preserved','compiler_and_cache_pins_preserved']):
        raise RuntimeError('Preservation scope narrowed')
    for name, pin in binding['files'].items():
        if digest(OUTPUT/name) != pin:
            raise RuntimeError('Full90 capsule drift')
    old = capsule(PARENT/'input-archive.tar.gz')
    new = capsule(OUTPUT/'input-archive.tar.gz')
    if validate_expansion(old, new) != binding['changed_files']:
        raise RuntimeError('Changed file identity drift')
    if new['capture-manifest.json'] != (OUTPUT/'capture-manifest.json').read_bytes():
        raise RuntimeError('Standalone manifest mismatch')
    import hashlib
    expected_auxiliary = {name: hashlib.sha256(new[name]).hexdigest().upper()
                          for name in ['fresh-integrated-axioms.lean', 'fresh-prior-a7-axioms.lean']}
    if binding['auxiliary_inputs'] != expected_auxiliary:
        raise RuntimeError('Fresh harness identity mismatch')
    print(json.dumps({'exact_material_expansion_verified': True, 'original_requests': 172,
                      'additional_request': REQUEST, 'local_compilation': False}))


if __name__ == '__main__':
    validate_successor()
