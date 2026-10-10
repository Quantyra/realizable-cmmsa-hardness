"""Freeze complete product-law bodies, argument and all unabridged prior reviews."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full107_prior_review_reuse import BASE, PARENT, HERE, LENSES, FRESH
from full107_consumption_v3_controller import ROOT


def read(path):
    return json.loads(path.read_bytes())


def main():
    reuse = read(BASE/'prior-review-reuse-audit.json')
    assert reuse['all344_per_lens_prior_body_coverage_identity_eligible']
    assert reuse['fresh_complete_bodies'] == FRESH and len(reuse['reports']) == 39
    index = read(BASE/'review-sources/source-index.json')
    assert index['project_body_count'] == 346 and len(index['roots']) == 260
    assert digest(BASE/'review-sources/source-index.json') == reuse['new_source_index_sha256']
    current = {row['path']: row for row in index['project_bodies']}
    parent = read(PARENT/'material-integration-v3/manifest.json')
    packet = parent['packets'][0]
    assert digest(packet['path']) == packet['sha256'] and len(packet['files']) == 92
    rows = []
    for original in packet['files']:
        row = dict(original)
        if row['source_kind'] == 'project':
            assert current[row['path']]['sha256'] == row['sha256']
            row['source_root'] = str(BASE/'review-sources')
        rows.append(row)
    for rel in FRESH:
        rows.append(dict(current[rel], source_kind='project', source_root=str(BASE/'review-sources')))
    old_boundaries = read(PARENT/'type-dag-qualification.json')['external_boundaries']
    new_boundaries = read(BASE/'type-dag-qualification.json')['external_boundaries']
    new_constants = sorted(set(new_boundaries)-set(old_boundaries))
    source_rows = {row['constant']: row['source'] for row in index['external_boundaries']}
    present = {row['path'] for row in rows}
    for name in new_constants:
        source = source_rows[name]
        if source['packet_path'] not in present:
            rows.append(dict(path=source['packet_path'], sha256=source['sha256'],
                             bytes=source['bytes'], source_kind='external',
                             source_root=str(BASE/'review-sources'), complete_body=True))
            present.add(source['packet_path'])
    assert len(rows) == len({row['path'] for row in rows})
    assert sum(row['source_kind'] == 'project' for row in rows) == 68
    header = '''FULL107 FULL346/FULL260/FOCUSED92 CONDITIONAL MATERIAL INTEGRATION REVIEW.
These instructions and current verified evidence supersede historical banners in immutable sources and reports. Native GREEN covers all346 captured sources,260 required standard-axiom profiles,seven stages0,zero owned warnings/errors and inherited regressions,699 actual objects and566 unchanged warm objects. Inherited warnings remain certification-policy debt. Complete native archive1A0CA7DF0B4C8994CE99FAC652380B70252EB3019059898D09622CB117676368 is39705927 bytes in two verified copies. Sole GCP metadata probe exited0; complete trace archive365E61C460F0F931C3F7047D393C48C8A8C2A326E282A2A8FB4066F5CB7522C9 is10205578 bytes in two verified copies. Dedicated02 independently TERMINATED. Full260/focused92 trace has8298 nodes,217 project modules,2767 external boundaries and zero unresolved entries. All344 parent sources and8269 parent native type/proof dependency nodes are byte/context identical; all39 original reviews are verified and supplied unabridged. This permits unchanged per-lens coverage reuse, not fresh346-body rereading.
Fresh required complete bodies are ActualFiniteFrameProductDuality.lean and its Checks. Inspect every declaration and proof, both directions where required, complete product argument and actual native axiom interfaces. Evaluate the three public exports as one coherent exact-product-energy milestone: guarded frame ratio duality, s-factor product identity, and unconditional append rank-projection energy. Validate i<=c+s, including i>c zero factors, s=0, zero width/rank, positive denominators, natural-to-real casts and exact orientation. The Full106 API argument repair changes only prod_div_distrib arity; all current Full107 bytes supplied here are compiled. Historical uncompiled-candidate banners remain immutable and do not supersede current receipts.
Retain actual SourceSize/HC46/dyadic and selected-leaf integration, spectral character pairing/tail-zero/orbits/counting/weaker+3 contract and exact normalization. The prior real frame-ratio energy law remains conditional on its explicit invariance/inverse/rank/carrier premises; new product law does not supply source or sampler witnesses. No complex-general energy, G/Phi composition, adjoint, complete packaged cross-level translation, unconditional hardness or manuscript acceptance is claimed.
Retain numeric NO/hfail/e/scalar, actual independent source/selection/global-table witness, joint arity/source/star/robust8S/pre-draw/sampling/encoded reduction/runtime/learning, exact upstream transports/postobjects, fresh source-object replay, inherited-warning certification and final provider/novelty/citation/BibTeX/TeX/PDF/manuscript gates. R14 remains HIGH. Classical append/Fourier/counting reconstruction carries no novelty/priority claim. MZ24 AppendixA13 supports a weaker bound; exact identities are reconstructed separately. Do not substitute uniform/rank-one noise, a smaller source/star family or a weaker conditional helper for an original obligation.
No tools,writes,Lean/Lake or subagents. Read all supplied complete bodies and arguments and all39 prior reports. Report declaration-specific severity,evidence,disposition and actions; distinguish mathematical soundness,native translation,conditional integration and overall readiness. State required fresh bodies skipped, report exact premises and residuals, and bar overall GO if any required body is skipped or HIGH remains. End with remaining to-do list.
'''
    pieces = [header.encode()]
    marker = read(ROOT.parent/'launch-once.json')
    native = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    assert read(native)['full107_expanded_native_gates_green']
    for label, path in [('CURRENT QUALIFIED NATIVE', native),
                        ('CURRENT QUALIFIED TRACE', BASE/'qualification-summary.json'),
                        ('CURRENT FULL344 REUSE AUDIT', BASE/'prior-review-reuse-audit.json'),
                        ('CURRENT FULL260/FOCUSED92 TOOLING', ROOT.parent/'consumption-preparation-v1-dag/readiness.json')]:
        pieces.append(('\n'+label+' SHA256 '+digest(path)+'\n').encode()+path.read_bytes())
    arguments = [Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp/actual-append-spectral-image-fibre-argument-2026-10-09.md'),
                 HERE/'frame-product-duality-candidate-v1/argument.md',
                 HERE/'frame-product-duality-candidate-v1/candidate.json']
    for path in arguments:
        pieces.append(('\nCOMPLETE CRITICAL ARGUMENT/IDENTITY '+path.name+' SHA256 '+digest(path)+'\n').encode()+path.read_bytes())
    for row in reuse['reports']:
        receipt = Path(row['path']); report = receipt.with_suffix('.md')
        assert digest(receipt) == row['receipt_sha256'] and digest(report) == row['report_sha256']
        pieces.append(('\nCOMPLETE PRESERVED REPORT '+row['folder']+' '+row['lens']+' SHA256 '+digest(report)+'\n').encode()+report.read_bytes())
    for row in rows:
        path = Path(row['source_root'])/row['path']
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
        pieces.append(('\n=== COMPLETE FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+path.read_bytes()+b'\n=== END COMPLETE FILE ===\n')
    text = b''.join(pieces)
    if len(text) >= 2500000:
        raise RuntimeError('Split complete review scope; do not truncate required evidence')
    destination = BASE/'material-integration-v3'
    destination.mkdir()
    output = destination/'integration.txt'; output.open('xb').write(text)
    result = dict(schema='full107-full346-full260-conditional-material-integration-v3',
                  required_lenses=LENSES, packets=[dict(path=str(output),sha256=digest(output),bytes=len(text),files=rows)],
                  parent_packet_sha256=packet['sha256'],source_index_sha256=digest(BASE/'review-sources/source-index.json'),
                  prior_review_reuse_sha256=digest(BASE/'prior-review-reuse-audit.json'),
                  prior_complete_project_bodies_identity_eligible=344,fresh_complete_project_bodies=2,
                  complete_supplied_bodies=len(rows),complete_supplied_project_bodies=68,
                  all39_prior_report_texts_unabridged=True,new_external_constants=new_constants,
                  roots=260,focused=92,source_scope=346,
                  qualified_trace_summary_sha256=digest(BASE/'qualification-summary.json'),
                  actual_provider_context_fit_verified=False,accepted=False,full_goal_complete=False)
    (destination/'manifest.json').open('x',encoding='utf-8').write(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(bytes=len(text),complete_bodies=len(rows),fresh_bodies=2,
                          sha256=digest(output),prior_reports=39,accepted=False)))


if __name__ == '__main__':
    main()
