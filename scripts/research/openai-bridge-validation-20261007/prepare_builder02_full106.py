"""Freeze the complete product-energy successor; this is not launch clearance."""
import copy
import io
import json
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_full106_product_energy_scope import HERE, PARENT, HARNESS, additions, make_successor

OUTPUT = PARENT.parent/'full106-exact-product-energy-resource02'
from prepare_builder02_full105 import REQUESTS as PARENT_REQUESTS
REQUESTS = PARENT_REQUESTS + additions()[1]


def main():
    from full105_capture_gates import validate_successor
    validate_successor()
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    custody = terminal['custody']
    qualified_path = check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    qualified = json.loads(qualified_path.read_bytes())
    assert digest(qualified_path) == 'CC11E2DA3B8A3FB372D5976BF615C066EE4071FBF7F2D7F9B2D1FA0A3B5CBE92'
    assert qualified['full105_expanded_native_gates_green']
    assert qualified['owned_warning_headers'] == [0]*7
    assert marker['run'] == terminal['run'] == stop['run'] and terminal['terminal']['compile_green']
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == '7237681467779354904'
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    old = capsule(PARENT/'input-archive.tar.gz')
    new = make_successor(old)
    sources, requests = additions()
    proposal_path = HERE/'full106-product-energy-scope-proposal-v1.json'
    proposal = json.loads(proposal_path.read_bytes())
    assert sha(new['capture-manifest.json']) == proposal['generated_manifest_sha256']
    assert sha(new[HARNESS]) == proposal['generated_harness_sha256']
    OUTPUT.mkdir(exist_ok=False)
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(schema='full106-full346-full260-exact-product-energy-v1', parent_run=marker['run'],
        parent_custody=custody, parent_qualified_report_sha256=digest(qualified_path), parent_qualified_green=True,
        added_sources=list(sources), additional_profiles=requests, repaired_sources=[],
        all344_parent_source_bytes_and257_profiles_preserved=True, all_seven_parent_stage_prefixes_preserved=True,
        entire346_source_graph_reachable=True, all_two_added_sources_owned=True,
        compiler_package_core_cache_configuration_preserved=True, scope_proposal_sha256=digest(proposal_path),
        native_verification_pending=True, independent_material_review_pending=True,
        exact_product_energy_native=False, G_Phi_laws_closed=False, numeric_NO_proven=False,
        R14='HIGH open', compiler_invoked=False, launch_clearance=False, accepted=False)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion, indent=2)+'\n').encode())
    binding = copy.deepcopy(json.loads((PARENT/'resource-binding.json').read_bytes()))
    binding.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'), changed_files=[HARNESS, 'capture-manifest.json'],
        added_files=list(sources), project_sources_preserved=344, additional_profiles=requests,
        auxiliary_inputs={name:sha(new[name]) for name in binding['auxiliary_inputs']},
        files={name:digest(OUTPUT/name) for name in ('input-archive.tar.gz', 'capture-manifest.json')})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(binding, indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=346, profiles=260,
        input_sha256=digest(OUTPUT/'input-archive.tar.gz'), manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
        launch_clearance=False, native_verified=False)))


if __name__ == '__main__':
    main()
