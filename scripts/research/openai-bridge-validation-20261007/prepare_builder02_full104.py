"""Freeze complete actual SourceSize/dyadic and exact-energy successor scope."""
import copy
import io
import json
import tarfile
from pathlib import Path
from custody_checks import digest,verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full103 import REQUESTS as PARENT_REQUESTS
from prepare_full104_consumer_energy_scope import HERE,PARENT,HARNESS,additions,make_successor,validate_expansion

OUTPUT=PARENT.parent/'full104-actual-consumer-exact-energy-resource02'
REQUESTS=PARENT_REQUESTS+additions()[1]


def main():
    from full103_capture_gates import validate_successor
    validate_successor()
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes());custody=terminal['custody']
    stop=json.loads((check/'vm-termination.json').read_bytes())
    q=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    qualified=json.loads(q.read_bytes())
    assert marker['run']==terminal['run']==stop['run'] and terminal['terminal']['compile_green']
    assert qualified['full103_expanded_native_gates_green']
    assert qualified['owned_warning_headers']==qualified['inherited_regression_headers']==[0]*7
    assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    reuse=HERE/'full104-static-candidate-review-reuse-v1.json'
    assert json.loads(reuse.read_bytes())['all_four_complete_candidate_files_have_three_lens_custody']
    old=capsule(PARENT/'input-archive.tar.gz');new=make_successor(old);sources,requests=additions()
    proposal=json.loads((HERE/'full104-consumer-energy-scope-proposal-v1.json').read_bytes())
    assert sha(new['capture-manifest.json'])==proposal['generated_manifest_sha256']
    assert sha(new[HARNESS])==proposal['generated_harness_sha256']
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz','x:gz') as archive:
        for name,data in sorted(new.items()):
            member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644
            archive.addfile(member,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion=dict(schema='full104-full344-full257-actual-consumer-exact-energy-v1',parent_run=marker['run'],
        parent_custody=custody,parent_qualified_report_sha256=digest(q),parent_qualified_green=True,
        added_sources=list(sources),additional_profiles=requests,repaired_sources=[],
        all340_parent_source_bytes_and251_profiles_preserved=True,all_seven_parent_stage_prefixes_preserved=True,
        entire344_source_graph_reachable=True,all_four_added_sources_owned=True,
        compiler_package_core_cache_configuration_preserved=True,scope_proposal_sha256=digest(HERE/'full104-consumer-energy-scope-proposal-v1.json'),
        prior_static_candidate_review_reuse_sha256=digest(reuse),parent_trace_pending=True,
        native_verification_pending=True,exact_s_factor_and_G_Phi_laws_closed=False,numeric_NO_proven=False,
        R14='HIGH open',compiler_invoked=False,launch_clearance=False,accepted=False)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion,indent=2)+'\n').encode())
    binding=copy.deepcopy(json.loads((PARENT/'resource-binding.json').read_bytes()))
    binding.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'),changed_files=[HARNESS,'capture-manifest.json'],
        added_files=list(sources),project_sources_preserved=340,additional_profiles=requests,
        auxiliary_inputs={name:sha(new[name]) for name in binding['auxiliary_inputs']},
        files={name:digest(OUTPUT/name) for name in ('input-archive.tar.gz','capture-manifest.json')})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(binding,indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz')==new
    print(json.dumps(dict(root=str(OUTPUT),sources=344,profiles=257,input_sha256=digest(OUTPUT/'input-archive.tar.gz'),
        manifest_sha256=digest(OUTPUT/'capture-manifest.json'),launch_clearance=False,native_verified=False)))


if __name__=='__main__':main()
