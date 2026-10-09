"""Freeze full327 conditional integration with both new bodies and all prior evidence."""
import json
from pathlib import Path
from custody_checks import digest
from full100_consumption_v2_controller import ROOT, ready

HERE = Path(__file__).parent
BASE = ROOT/'qualification'
OLD = ROOT.parent.parent/'full97-spectral-bridge-utf8-section-repair-resource02/consumption-v1/qualification'

def main():
    loaded, runner, binding = ready()
    reuse=json.loads((BASE/'prior-review-reuse-audit.json').read_bytes())
    index=json.loads((BASE/'review-sources/source-index.json').read_bytes())
    assert reuse['reuse_identity_eligible'] and len(reuse['unchanged_prior_complete_bodies'])==325
    assert reuse['shared_native_constant_types_and_edges_unchanged']==8072
    assert len(reuse['new_or_changed_complete_bodies'])==2 and index['project_body_count']==327 and len(index['roots'])==192
    parent=json.loads((OLD/'material-integration-v1/manifest.json').read_bytes())
    packet=parent['packets'][0];path=Path(packet['path']);assert digest(path)==packet['sha256']
    header=b'''FULL100 FULL327/FULL192/FOCUSED24 CONDITIONAL MATERIAL INTEGRATION REVIEW.
These current instructions supersede every historical FULL97/FULL95/FULL90 instruction preserved below. Exact current scope:327 captured complete project bodies,192 required standard profiles,all seven native stages0,661 actual compiled objects,full192/focused24 qualified trace,8084 exact type-DAG nodes,202 consumed project modules,2740 external boundaries and zero unresolved in both graphs.325 prior complete bodies have verified per-lens review provenance and identical source/compiler/package/core/cache/configuration context;8072 shared native constant types/type/proof/union edges are unchanged. Identity reuse is permitted, but absent bodies were not freshly reread. R14 encoded runtime/reduction remains HIGH outside conditional integration. Preserve all previous open findings and claims boundaries.
Inspect every supplied complete source and every declaration of the two new files BinaryMatrixRightOrbit.lean and BinaryMatrixRightFourierCovariance.lean. The current packet preserves all70 prior complete sources (47 project/23 Complexitylib), adds both complete new sources and full pinned Mathlib Matrix/Rank, Matrix/ToLin and FieldTheory/Finiteness. The complete327/409 external source corpus is indexed and preserved; availability is not fresh semantic review. Identify supplied bodies inspected/skipped and separate inherited review reuse from new coverage.
Audit all dimensions, deficient maps, zero dimensions, paired-inverse matrix orientation, toLin'/toMatrix' directions, range restrictions and subtype equality, rightBasisEquiv inverse laws, pairing/character transpose direction, finite mean reindexing/cardinality normalization, and Fourier coefficient equality under all original invariance hypotheses. Current native GREEN covers these declarations only, not a universal Spectral47 inhabitant. Typed .lean source and .olean object hashes are different categories; use the explicit mapping and preserve the settled historical H1 category error.
Review full conditional integration with actual I/copies/U/A/C/T/f, source rows independent of leaf count, original SourceSize/HC46/dyadic consumers and all original height/rank/dimension/harness guards. Do not replace actual append by uniform/rank-one noise or narrow source/star families. Technical source-body selection is distinct from mathematical pre-draw source/selection/global-table witnesses. The full source/dependency/native context and old reports below are bounded evidence, not accepted upstream CMMSA bridges.
The separate complete spectral argument and three actual argument-review reports are supplied as proposals/assessment. All found it sufficient for the exact Lean contract, with native/final readiness open. Confirm Matrix.rank equals finrank of the toLin' range using supplied complete sources; inspect the actual coordinate-equivalence/append definitions present in the historical complete source packet; inspect the supplied source alignment audit. Distinguish closing those input/body gaps from manuscript Lemma4.7 alignment, universal count/energy/gain/contract proof and final acceptance, which remain open. Recommended simpler counting/injection methods must retain the same full universal target and all original guards.
Universal Spectral47,HC46 actual contract inhabitant,useful numeric NO/hfail/e,actual joint source/selector/star/robust8S/pre-draw table,physical sampler,encoded reduction/runtime/learning,exact upstream transports,warning/fresh-checkout certification,novelty/citations/PDF/publication remain open. No overall GO,unconditional material/hardness theorem,priority or manuscript acceptance is requested. Preserve inherited baseline warnings despite zero owned/regression gates. Stale uncompiled banners are historical captured bytes; do not treat them as current status or mutate immutable inputs.
No tools,writes,Lean/Lake or subagents. Give declaration-specific severity,evidence,disposition and actions. Report conditional integration separately from overall readiness. Any skipped required fresh body or unresolved HIGH bars overall GO. End with remaining to-do list.
'''
    pieces=[header]
    marker=json.loads((ROOT.parent/'launch-once.json').read_bytes())
    native=Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    for label,p in [('CURRENT QUALIFIED NATIVE',native),('CURRENT QUALIFIED TRACE',BASE/'qualification-summary.json'),
                    ('CURRENT FULL325 SOURCE/TYPE/PROOF REUSE',BASE/'prior-review-reuse-audit.json'),
                    ('CURRENT COMPLETE SOURCE ALIGNMENT',HERE/'full100-actual-spectral-source-alignment-v1.json'),
                    ('PRIOR FULL97 ROOT RECONCILIATION',OLD/'material-review-root-reconciliation-v1.json'),
                    ('ARGUMENT ROOT RECONCILIATION',HERE/'full100-spectral-argument-reports/root-reconciliation-v1.json')]:
        pieces.append(('\n'+label+' SHA256 '+digest(p)+'\n').encode()+p.read_bytes())
    assert digest(native)==binding['qualified_report_sha256']
    for folder in ['full97-material-integration-reports','full100-spectral-argument-reports']:
        for lens in parent['required_lenses']:
            p=HERE/folder/(lens+'-01.md');r=json.loads(p.with_suffix('.json').read_bytes())
            assert digest(p)==r['report_sha256'] and r['native_exit']==0 and r['actual_packet_context_fit']
            pieces.append(('\nPRESERVED COMPLETE REPORT '+folder+' '+lens+' SHA256 '+digest(p)+'\n').encode()+p.read_bytes())
    argument_manifest=json.loads((ROOT/'spectral-argument-review-v1/manifest.json').read_bytes())
    argument_packet=Path(argument_manifest['packets'][0]['path'])
    assert digest(argument_packet)==argument_manifest['packets'][0]['sha256']
    # Preserve the exact original reviewed argument bytes rather than an edited planning follow-up.
    import subprocess
    argument=subprocess.check_output(['git','show',argument_manifest['planning_head']+':'+argument_manifest['argument_path']],
        cwd='C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
    import hashlib
    assert hashlib.sha256(argument).hexdigest().upper()==argument_manifest['argument_sha256']
    pieces.append(b'\nCOMPLETE ORIGINAL REVIEWED CRITICAL ARGUMENT\n'+argument)
    # Historical evidence wrappers and all70 complete source bodies remain unabridged.
    pieces.append(b'\nBEGIN PRESERVED HISTORICAL FULL97 PACKET (CURRENT HEADER ABOVE GOVERNS)\n'+path.read_bytes()+b'\nEND PRESERVED HISTORICAL PACKET\n')
    rows=list(packet['files']);supplied={r['path'] for r in rows}
    current={r['path']:r for r in index['project_bodies']}
    for row in rows:
        p=Path(row['source_root'])/row['path']
        assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes']
        if row['source_kind']=='project':assert current[row['path']]['sha256']==row['sha256']
    additional=[]
    for rel in reuse['new_or_changed_complete_bodies']:
        additional.append(dict(current[rel],source_kind='project',source_root=str(BASE/'review-sources')))
    for rel in ['LinearAlgebra/Matrix/Rank.lean','LinearAlgebra/Matrix/ToLin.lean','FieldTheory/Finiteness.lean']:
        p=BASE/'review-sources/external/Mathlib'/rel
        additional.append(dict(path='external/Mathlib/'+rel,source_kind='Mathlib',source_root=str(BASE/'review-sources'),sha256=digest(p),bytes=p.stat().st_size))
    for row in additional:
        assert row['path'] not in supplied
        p=Path(row['source_root'])/row['path'];assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes']
        pieces.append(('\n=== COMPLETE FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+p.read_bytes()+b'\n=== END COMPLETE FILE ===\n')
        rows.append(row);supplied.add(row['path'])
    text=b''.join(pieces)
    assert len(rows)==75 and sum(r['source_kind']=='project' for r in rows)==49
    if len(text)>=1800000:raise RuntimeError('Do not truncate: split complete source packets with full integration evidence')
    destination=BASE/'material-integration-v1';destination.mkdir()
    output=destination/'integration.txt'
    with output.open('xb') as stream:stream.write(text)
    value=dict(schema='full100-full192-two-new-body-conditional-material-integration-v1',required_lenses=parent['required_lenses'],
        packets=[dict(path=str(output),sha256=digest(output),bytes=len(text),files=rows)],
        parent_packet_sha256=packet['sha256'],source_index_sha256=digest(BASE/'review-sources/source-index.json'),
        prior_complete_project_bodies_identity_eligible=325,new_complete_project_bodies=2,
        complete_supplied_bodies=75,complete_supplied_project_bodies=49,complete_supplied_Complexitylib_bodies=23,complete_supplied_Mathlib_bodies=3,
        roots=192,focused=24,source_scope=327,prior_raw_report_chain_unabridged=True,
        actual_provider_context_fit_verified=False,accepted=False,full_goal_complete=False)
    with (destination/'manifest.json').open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(bytes=len(text),complete_bodies=75,fresh_bodies=2,sha256=digest(output),accepted=False)))

if __name__=='__main__':main()
