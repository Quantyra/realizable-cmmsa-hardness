"""Freeze missing full Fourier body and actual object/graph/member evidence."""
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from full100_consumption_v2_controller import ROOT, ready

HERE=Path(__file__).parent
BASE=ROOT/'qualification'
OLD=ROOT.parent.parent/'full97-spectral-bridge-utf8-section-repair-resource02/consumption-v1/qualification'

def read(p):return json.loads(Path(p).read_bytes())

def main():
    loaded,runner,binding=ready()
    current=read(BASE/'graphs/validated-graphs.json');prior=read(OLD/'graphs/validated-graphs.json')
    dag=read(BASE/'type-dag-qualification.json')
    added=sorted(set(current['nodes'])-set(prior['nodes']));assert len(added)==12
    new_boundaries=sorted(set(dag['external_boundaries'])-set(read(OLD/'type-dag-qualification.json')['external_boundaries']))
    assert len(new_boundaries)==2
    nm=read(ROOT.parent/'launch-once.json');nc=read(Path(nm['preflight'])/'terminal-custody.json')['custody']
    tm=read(ROOT/'launch-once.json');tc=read(Path(tm['preflight'])/'terminal-custody.json')
    c=tc['custody']
    for custody in [nc,c]:verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    with tarfile.open(nc['repository_path']) as native:
        objects=json.loads(native.extractfile('object-after.json').read())
        native_members=[dict(name=m.name,bytes=m.size) for m in native.getmembers() if m.isfile()]
    with tarfile.open(c['repository_path']) as trace:
        terminal=json.loads(trace.extractfile('terminal.json').read())
        trace_members=[dict(name=m.name,bytes=m.size) for m in trace.getmembers() if m.isfile()]
    assert len(objects)==661 and terminal==tc['probe_terminal']
    assert terminal['compiled_objects_preserved']==661 and terminal['project_sources_preserved']==327
    assert terminal['native_archive_sha256']==nc['remote_sha256'] and terminal['probe_native_exit']==0 and terminal['failure'] is None
    manifest=read(ROOT.parent/'capture-manifest.json')
    expected={'.lake/build/lib/lean/'+p.removeprefix('lean/').removesuffix('.lean')+'.olean' for p in manifest['project_sources']}
    assert len(expected)==327 and expected<=set(objects)
    index=read(BASE/'review-sources/source-index.json')
    external={r['source']['packet_path']:r['source'] for r in index['external_boundaries']}
    file_members=[]
    for rel in ['external/Mathlib/LinearAlgebra/Matrix/Rank.lean','external/Mathlib/LinearAlgebra/Matrix/ToLin.lean','external/Mathlib/FieldTheory/Finiteness.lean']:
        row=external[rel];p=BASE/'review-sources'/rel;assert row['packet_path']==rel and digest(p)==row['sha256'] and p.stat().st_size==row['bytes'];file_members.append(dict(row))
    rel='lean/PvNP/RealizableHardness/BinaryMatrixFourier.lean';p=BASE/'review-sources'/rel;pin=manifest['project_sources'][rel]
    assert digest(p)==pin['sha256'] and p.stat().st_size==pin['bytes']
    evidence=dict(schema='full100-actual-native-trace-object-and-added-node-members-v1',
        native_custody=nc,trace_custody=c,native_archive_members=native_members,trace_archive_members=trace_members,
        actual_native_object_count=len(objects),actual_project_olean_count=len(expected),all_project_oleans_present=True,
        native_object_after_inventory=objects,object_after_inventory_source='exact object-after.json member of verified native custody archive',
        trace_terminal=terminal,trace_preservation_checks_bound_to_native_object_inventory=True,
        new_native_nodes={name:dict(current['nodes'][name],exact_type_dag_sha256=dag['type_dag_sha256'][name]) for name in added},
        new_external_boundaries={name:dag['external_boundaries'][name] for name in new_boundaries},
        exact_complete_source_index_members=file_members,source_index_sha256=digest(BASE/'review-sources/source-index.json'),
        compiled_object_binary_archive_claimed=False,fresh_checkout_replay_completed=False,
        universal_Spectral47_inhabitant_proven=False,accepted=False,full_goal_complete=False)
    destination=BASE/'identity-addendum-v1';destination.mkdir()
    ep=destination/'actual-members-and-identities.json'
    with ep.open('x',encoding='utf-8') as stream:json.dump(evidence,stream,indent=2);stream.write('\n')
    text=b'''FULL100 INTEGRATION IDENTITY/BODY ADDENDUM; PRESERVED ORIGINAL REPORTS REMAIN UNCHANGED.
Close only the specific evidence gaps raised by the three original integration reports: ALN-2/NC100-7/CX100-08 (complete BinaryMatrixFourier body), NC100-8 (actual661 native objects), CX100-12 (+12 nodes/+2 boundaries enumeration), and exact membership of the three supplied Mathlib sources in the complete409-file index. Original conditional GO-WITH-NOTES and all broader HIGH/Medium findings remain preserved. No universal Spectral47,unconditional theorem,numeric NO,source/runtime witness,fresh-checkout replay,compiled-object binary archive,manuscript fidelity or overall GO follows.
Inspect the complete Fourier body and rederive pairing/character/uniformMean/fourierCoeff/rankProjection/Parseval and their exact normalization. Compare its exact source identity to the unchanged Full100 capture. Verify typed source/object categories separately. The supplied actual native object-after inventory is661 entries and contains every one of the327 expected project .olean paths; the actual GCP trace terminal confirms661 objects/327 sources preserved and binds that native archive. This resolves the count at the inventory/terminal evidence tier, not by archiving the actual .olean binaries. The raw archive member lists are explicit. Fresh-checkout replay remains separate debt.
Inspect all twelve added native nodes with type-DAG digests/type/proof/union edges and both added external boundaries; do not infer them from counts. Exact three-source index member records include source/package/revision identities already root-verified. No tools,writes,Lean/Lake or subagents. Report inspected/skipped body,each original finding disposition,remaining limitations,and conditional integration versus overall readiness separately. End with remaining to-do list.
'''
    for lens in ['proof-adversarial','complexity','non-claims']:
        report=HERE/'full100-material-integration-reports'/(lens+'-01.md');r=read(report.with_suffix('.json'))
        assert digest(report)==r['report_sha256'] and r['native_exit']==0 and r['actual_packet_context_fit']
        text+=('\nCOMPLETE ORIGINAL FULL100 REPORT '+lens+' SHA256 '+digest(report)+'\n').encode()+report.read_bytes()
    text+=('\nACTUAL MEMBER/OBJECT/NODE EVIDENCE SHA256 '+digest(ep)+'\n').encode()+ep.read_bytes()
    text+=('\n=== COMPLETE FILE '+rel+' SHA256 '+digest(p)+' ===\n').encode()+p.read_bytes()+b'\n=== END COMPLETE FILE ===\n'
    output=destination/'addendum.txt'
    with output.open('xb') as stream:stream.write(text)
    value=dict(schema='full100-complete-Fourier-and-actual-identity-addendum-v1',required_lenses=['proof-adversarial','complexity','non-claims'],
        packets=[dict(path=str(output),sha256=digest(output),bytes=len(text),files=[dict(path=rel,source_root=str(BASE/'review-sources'),source_kind='project',sha256=digest(p),bytes=p.stat().st_size)])],
        evidence_sha256=digest(ep),actual_object_count=661,added_nodes=12,added_boundaries=2,
        original_reports_preserved=True,accepted=False,full_goal_complete=False)
    with (destination/'manifest.json').open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(bytes=len(text),sha256=digest(output),objects=661,new_nodes=12,new_boundaries=2,accepted=False)))

if __name__=='__main__':main()
