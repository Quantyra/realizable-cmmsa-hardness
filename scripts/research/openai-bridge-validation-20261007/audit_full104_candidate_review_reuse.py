"""Verify prior complete static candidate review custody, without native claims."""
import json
from pathlib import Path
from custody_checks import digest
from prepare_full104_consumer_energy_scope import HERE


def main():
    groups = [('spectral-exact-energy-candidate-v1','candidate.json','exact-spectral-operator-reports'),
              ('sourcesize-spectral-application-candidate-v2','derivation.json','sourcesize-spectral-delta-review-reports')]
    records=[]
    for folder,metadata,reports in groups:
        files=json.loads((HERE/folder/metadata).read_bytes())['files']
        for lens in ('proof-adversarial','complexity','non-claims'):
            report=HERE/reports/(lens+'-01.md')
            receipt_path=report.with_suffix('.json');receipt=json.loads(receipt_path.read_bytes())
            assert digest(report)==receipt['report_sha256'] and report.stat().st_size>0
            assert receipt['native_exit']==0 and receipt['actual_packet_context_fit']
            raw_path=Path(receipt['raw_stdout_path'])
            assert digest(raw_path)==receipt['raw_stdout_sha256']
            raw=json.loads(raw_path.read_bytes())
            assert not raw.get('is_error') and raw['num_turns']==1
            manifest_path=raw_path.parent.parent/'manifest.json'
            manifest=json.loads(manifest_path.read_bytes());packet=manifest['packets'][0]
            assert digest(packet['path'])==packet['sha256']==receipt['packet_sha256']
            assert Path(packet['path']).stat().st_size==packet['bytes']
            assert packet['files']==receipt['supplied_complete_files']
            packet_data=Path(packet['path']).read_bytes()
            rows=[]
            for row in files:
                candidate=HERE/folder/Path(row['path']).name
                assert digest(candidate)==row['sha256'] and candidate.stat().st_size==row['bytes']
                assert packet_data.count(candidate.read_bytes())==1,'Complete exact candidate bytes must be present in actual packet'
                matches=[r for r in packet['files'] if r['path'].endswith(row['path']) and r['sha256']==row['sha256'] and r['bytes']==row['bytes']]
                assert len(matches)==1,'Exact complete candidate body must occur once in prior packet'
                rows.append(dict(path=row['path'],sha256=row['sha256'],bytes=row['bytes'],prior_packet_path=matches[0]['path']))
            records.append(dict(candidate=folder,lens=lens,report_path=str(report),report_sha256=digest(report),
                receipt_sha256=digest(receipt_path),raw_stdout_path=str(raw_path),raw_stdout_sha256=digest(raw_path),
                packet_sha256=packet['sha256'],complete_candidate_files=rows,native_exit=0,
                actual_packet_context_fit=True,one_turn=True))
    result=dict(schema='full104-exact-static-candidate-review-reuse-v1',reviews=records,
        all_four_complete_candidate_files_have_three_lens_custody=True,source_bytes_unchanged=True,
        review_tier='Prior static body and mathematical/composition inspection only; historical native labels retained',
        fresh_dependency_body_review_claimed=False,native_compilation_and_profiles_and_consumption_trace_pending=True,
        post_kernel_full_scope_integration_review_pending=True,exact_s_factor_and_G_Phi_and_adjoint_translation_open=True,
        numeric_NO_proven=False,R14='HIGH open',accepted=False,full_goal_complete=False)
    data=(json.dumps(result,indent=2)+'\n').encode();out=HERE/'full104-static-candidate-review-reuse-v1.json'
    if out.exists():assert out.read_bytes()==data
    else:out.write_bytes(data)
    print(json.dumps(dict(verified_reviews=len(records),candidate_files=4,lenses=3,
        review_reuse_sha256=digest(out),fresh_native_acceptance=False)))


if __name__=='__main__':main()
