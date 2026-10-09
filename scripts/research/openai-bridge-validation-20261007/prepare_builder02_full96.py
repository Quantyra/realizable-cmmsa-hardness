"""Freeze additive right-orbit and explicit contract bridges; no launch or local Lean."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest,verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full95 import OUTPUT as PARENT
HERE=Path(__file__).parent
OUTPUT=PARENT.parent/'full96-spectral-orbit-contract-bridge-resource02'
CANDIDATES=HERE/'full96-spectral-bridge-candidates-v1'
MODULES=['PvNP.RealizableHardness.BinaryMatrixSameRangeOrbit','PvNP.RealizableHardness.SourceSizeContractBridge']
ADDED=['lean/'+m.replace('.','/')+'.lean' for m in MODULES]
REQUESTS=[MODULES[0]+'.same_range_right_orbit',MODULES[1]+'.hc46_contract_iff',MODULES[1]+'.spectral47_contract_iff']
HARNESS='fresh-integrated-axioms.lean'
IMPORTS=''.join('import '+m+'\n' for m in MODULES).encode()
PRINTS=''.join('#print axioms '+r+'\n' for r in REQUESTS).encode()

def parent_custody():
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
    custody=terminal['custody'];verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    assert custody['remote_sha256']=='E48640AC66338FE792BED8400BF24F7EC947C4B80CB1687CC3992CFACE126EE2'
    assert terminal['terminal']['compile_green'] and stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    assert marker['run']==terminal['run']==stop['run']
    report=check/'qualified-native'/marker['run']/'material-expanded-native-report.json';d=json.loads(report.read_bytes())
    assert digest(report)=='6F164D490EB324613FA286598FF635F84CF45B0B9A88450885E4F7A43D9D43DA'
    assert d['full95_expanded_native_gates_green'] and d['all_seven_stage_exits']==[0]*7
    assert d['expanded_requested_axiom_count']==181 and d['project_closure_sources']==323
    assert d['owned_warning_headers']==d['inherited_regression_headers']==[0]*7
    q=PARENT/'consumption-v1/qualification'
    trace=json.loads((q/'qualification-summary.json').read_bytes());root=json.loads((q/'material-review-root-reconciliation-v1.json').read_bytes())
    assert trace['structural_trace_qualification'] and all(v==0 for v in trace['unresolved_by_graph'].values())
    assert root['original_and_addendum_reports_read_in_full'] and root['source_object_category_finding_closed_by_each_lens']
    assert not root['full_goal_complete'] and root['all_three_material_verdicts']=='GO-WITH-NOTES, conditional'
    for row in root['reports']:
        receipt=json.loads(Path(row['receipt_path']).read_bytes());assert digest(row['receipt_path'])==row['receipt_sha256']
        assert receipt['report_sha256']==row['report_sha256'] and receipt['actual_packet_context_fit'] and receipt['native_exit']==0
    settled=q/'six-review-custody-v1/typed-custody-settlement.json';review=json.loads(settled.read_bytes());c=review['custody']
    verify_local_custody(c['short_path'],c['repository_path'],c['short_sha256'],c['bytes'])
    assert review['provider_reports']==6 and review['builder02_status']=='TERMINATED'
    return marker,custody,report,q,settled

def make_successor(old):
    new=dict(old);manifest=json.loads(old['capture-manifest.json'])
    for rel,module in zip(ADDED,MODULES):
        data=(CANDIDATES/(module.rsplit('.',1)[-1]+'.lean')).read_bytes()
        new[rel]=data;manifest['project_sources'][rel]={'sha256':sha(data),'bytes':len(data)}
    new[HARNESS]=IMPORTS+old[HARNESS]+PRINTS
    manifest['requested_axioms']+=REQUESTS
    manifest['stages'][4]['argv']+=MODULES
    new['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    validate_expansion(old,new);return new

def validate_expansion(old,new):
    assert set(new)==set(old)|set(ADDED),'Source scope changed'
    assert sorted(n for n in old if old[n]!=new[n])==sorted([HARNESS,'capture-manifest.json']),'Existing source or control changed'
    assert new[HARNESS]==IMPORTS+old[HARNESS]+PRINTS,'Harness scope/imports changed'
    a=json.loads(old['capture-manifest.json']);b=json.loads(new['capture-manifest.json'])
    assert len(a['project_sources'])==323 and len(b['project_sources'])==325
    assert len(a['requested_axioms'])==181 and b['requested_axioms']==a['requested_axioms']+REQUESTS and len(set(b['requested_axioms']))==184
    assert len(a['stages'])==len(b['stages'])==7 and b['stages'][4]['argv']==a['stages'][4]['argv']+MODULES
    for rel,module in zip(ADDED,MODULES):
        candidate=(CANDIDATES/(module.rsplit('.',1)[-1]+'.lean')).read_bytes()
        assert new[rel]==candidate
        assert b['project_sources'][rel]=={'sha256':sha(candidate),'bytes':len(candidate)}
    normalized=copy.deepcopy(b)
    for rel in ADDED:normalized['project_sources'].pop(rel)
    normalized['requested_axioms']=a['requested_axioms'];normalized['stages'][4]=a['stages'][4]
    assert normalized==a,'Manifest changed beyond exact additive source/profile/stage scope'
    modules={rel.removeprefix('lean/').removesuffix('.lean').replace('/','.'):rel for rel in b['project_sources']}
    def imports(data):return [m for m in re.findall(r'^import (\S+)',data.decode(),re.M) if m in modules]
    pending=imports(new[HARNESS]);reached=set()
    while pending:
        m=pending.pop()
        if m in reached:continue
        reached.add(m);pending.extend(imports(new[modules[m]]))
    assert reached==set(modules),'Complete325 project import closure is required'
    for request in b['requested_axioms']:
        owner=max((m for m in modules if request.startswith(m+'.')),key=len);assert owner in reached
    return True

def main():
    from full95_capture_gates import validate_successor
    validate_successor();marker,custody,report,q,settled=parent_custody()
    binding=json.loads((PARENT/'resource-binding.json').read_bytes())
    for name,pin in binding['files'].items():assert digest(PARENT/name)==pin
    assert digest(PARENT/'input-archive.tar.gz')=='4BC7F2B3D0129A449A8CB90163970377D1E08ADC27CB708B48AF17E5896CA441'
    old=capsule(PARENT/'input-archive.tar.gz');new=make_successor(old)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz','x:gz') as archive:
        for name,data in sorted(new.items()):
            member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644;archive.addfile(member,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion=dict(schema='full96-additive-right-orbit-contract-bridge-v1',parent_run=marker['run'],parent_custody=custody,
        parent_qualified_report_sha256=digest(report),parent_trace_qualification_sha256=digest(q/'qualification-summary.json'),
        parent_review_root_reconciliation_sha256=digest(q/'material-review-root-reconciliation-v1.json'),parent_review_custody_sha256=digest(settled),
        repaired_sources=[],added_sources=ADDED,additional_profiles=REQUESTS,all323_parent_source_bytes_preserved=True,
        all181_parent_requests_preserved=True,original_seven_stages_preserved_as_prefixes=True,
        compiler_packages_core_cache_configs_preserved=True,candidate_derivation_sha256=digest(CANDIDATES/'derivation.json'),
        Spectral47_inhabitant_constructed=False,local_compilation=False,native_verification_pending=True,launch_clearance=False,accepted=False,full_goal_complete=False)
    (OUTPUT/'source-expansion.json').write_text(json.dumps(expansion,indent=2)+'\n',encoding='utf-8')
    successor=copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'),changed_files=[HARNESS,'capture-manifest.json'],added_files=ADDED,
        project_sources_preserved=323,additional_profiles=REQUESTS,
        auxiliary_inputs={n:sha(new[n]) for n in binding['auxiliary_inputs']},
        files={n:digest(OUTPUT/n) for n in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor,indent=2)+'\n',encoding='utf-8')
    assert capsule(OUTPUT/'input-archive.tar.gz')==new
    print(json.dumps({'root':str(OUTPUT),'sources':325,'profiles':184,'input_sha256':digest(OUTPUT/'input-archive.tar.gz'),'launch_clearance':False,'accepted':False}))
if __name__=='__main__':main()
