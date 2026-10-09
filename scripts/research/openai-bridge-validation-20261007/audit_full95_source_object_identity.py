"""Reconcile source-byte identities with separately typed compiled-object identities."""
import hashlib
import json
from pathlib import Path
import tarfile
from prepare_builder02_full95 import OUTPUT
from custody_checks import verify_local_custody, digest

def main():
    marker=json.loads((OUTPUT/'launch-once.json').read_bytes())
    check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes())
    custody=terminal['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    report_path=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    report=json.loads(report_path.read_bytes())
    manifest=json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    assert report['full95_expanded_native_gates_green'] and report['all_seven_stage_exits']==[0]*7
    assert len(manifest['project_sources'])==323 and len(manifest['requested_axioms'])==181
    q=OUTPUT/'consumption-v1/qualification'
    review=json.loads((q/'material-integration-v1/manifest.json').read_bytes())
    source_index=json.loads((q/'review-sources/source-index.json').read_bytes())
    reuse=json.loads((q/'prior-review-reuse-audit.json').read_bytes())
    trace_marker=json.loads((OUTPUT/'consumption-v1/launch-once.json').read_bytes())
    trace=json.loads((Path(trace_marker['preflight'])/'terminal-custody.json').read_bytes())
    trace_custody=trace['custody']
    verify_local_custody(trace_custody['short_path'],trace_custody['repository_path'],trace_custody['remote_sha256'],trace_custody['bytes'])
    assert trace['probe_terminal']['probe_native_exit']==0 and trace['probe_terminal']['failure'] is None
    assert (trace['probe_terminal']['project_sources_preserved'],trace['probe_terminal']['compiled_objects_preserved'])==(323,653)
    source_rows={r['path']:r for r in source_index['project_bodies']}
    packet_rows={r['path']:r for r in review['packets'][0]['files'] if r['source_kind']=='project'}
    with tarfile.open(custody['repository_path']) as archive:
        def read(name):return json.loads(archive.extractfile(name).read())
        before=read('source-before.json');after=read('source-after.json')
        compiled=read('compiled-project-objects.json');objects=read('object-after.json')
        expected={rel:row['sha256'] for rel,row in manifest['project_sources'].items()}
        expected.update({rel:row['sha256'] for rel,row in manifest['configs'].items()})
        assert before==after==expected and len(compiled)==323 and len(objects)==653
        artifact_pins={name:hashlib.sha256(archive.extractfile(name).read()).hexdigest().upper() for name in ['capture-manifest.json','source-before.json','source-after.json','compiled-project-objects.json','object-after.json']}
    rows=[]
    with tarfile.open(OUTPUT/'input-archive.tar.gz') as inputs:
        for rel in reuse['new_or_changed_complete_bodies']:
            source=inputs.extractfile(rel).read();pin=hashlib.sha256(source).hexdigest().upper()
            assert len(source)==manifest['project_sources'][rel]['bytes'] and pin==manifest['project_sources'][rel]['sha256']==before[rel]==after[rel]
            assert source==(q/'review-sources'/rel).read_bytes()
            assert packet_rows[rel]['sha256']==source_rows[rel]['sha256']==pin
            object_path='.lake/build/lib/lean/'+rel.removeprefix('lean/').removesuffix('.lean')+'.olean'
            assert compiled[object_path]==objects[object_path]==report['added_object_hashes'][rel]
            rows.append(dict(source_path=rel,source_bytes=len(source),source_sha256=pin,
                compiled_object_path=object_path,compiled_object_sha256=objects[object_path],
                frozen_input_review_packet_and_native_before_after_source_identity=True,
                compiled_project_inventory_and_object_after_and_qualified_report_identity=True,
                native_all_stages_zero=True,trace_source_and_object_seals_preserved=True))
    original172=manifest['requested_axioms'][:172]
    full90=json.loads((OUTPUT.parent/'full90-material-resource02/capture-manifest.json').read_bytes())['requested_axioms']
    assert manifest['requested_axioms'][:173]==full90 and len(full90)==173
    assert len(original172)+len(report['added_requested_axioms'])==181
    assert manifest['requested_axioms'][172:]==report['added_requested_axioms']
    result=dict(schema='full95-typed-source-object-identity-reconciliation-v1',run=marker['run'],
        explanation='Source SHA-256 hashes UTF-8 .lean file bytes. Object SHA-256 hashes different .olean binary bytes. Equality across those categories is not expected. The verified mapping ties reviewed source bytes to the exact native before/after source seals and corresponding freshly compiled object inventory.',
        native_custody=custody,trace_custody=trace_custody,
        capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),
        qualified_report_sha256=digest(report_path),native_archive_member_pins=artifact_pins,mappings=rows,
        request_bookkeeping=dict(frozen_original=172,full90=173,full95=181,added_since_original=9,added_since_full90=8,original173_order_preserved=True),
        phase_bookkeeping='Native qualification flags recorded before trace/body recovery are historical. Later qualified trace/source-index/reuse records establish those later steps; original reports were not rewritten.',
        source_normalization_or_repair_performed=False,compiler_invoked=False,reviewer_H1_disposition_pending=True,
        independent_acceptance=False,full_goal_complete=False)
    path=q/'source-object-identity-reconciliation-v1.json'
    with path.open('x',encoding='utf-8') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'mappings':len(rows),'source_object_custody_verified':True,'path':str(path),'sha256':digest(path)}))
if __name__=='__main__':main()
