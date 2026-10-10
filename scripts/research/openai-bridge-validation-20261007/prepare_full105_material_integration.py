"""Freeze complete changed bodies and unabridged prior review evidence."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full105_prior_review_reuse import BASE, PARENT, HERE, LENSES
from full105_consumption_v3_controller import ROOT


def main():
    reuse = json.loads((BASE/'prior-review-reuse-audit.json').read_bytes())
    assert reuse['all340_per_lens_prior_body_coverage_identity_eligible']
    assert len(reuse['fresh_complete_bodies']) == 4 and len(reuse['reports']) == 36
    index = json.loads((BASE/'review-sources/source-index.json').read_bytes())
    assert index['project_body_count'] == 344 and len(index['roots']) == 257
    assert digest(BASE/'review-sources/source-index.json') == reuse['new_source_index_sha256']
    current = {row['path']:row for row in index['project_bodies']}
    parent = json.loads((PARENT/'material-integration-v3/manifest.json').read_bytes())
    packet = parent['packets'][0]
    assert digest(packet['path']) == packet['sha256'] and len(packet['files']) == 88
    rows = []
    for row in packet['files']:
        row = dict(row)
        if row['source_kind'] == 'project':
            assert current[row['path']]['sha256'] == row['sha256']
            row['source_root'] = str(BASE/'review-sources')
        rows.append(row)
    for rel in reuse['fresh_complete_bodies']:
        rows.append(dict(current[rel], source_kind='project', source_root=str(BASE/'review-sources')))
    assert len(rows) == len({row['path'] for row in rows}) == 92
    assert sum(row['source_kind'] == 'project' for row in rows) == 66
    header = '''FULL105 FULL344/FULL257/FOCUSED89 CONDITIONAL MATERIAL INTEGRATION REVIEW.
These current instructions and exact verified evidence supersede historical banners in preserved reports. Qualified native GREEN covers all344 captured sources,257 required standard-axiom profiles,seven stage exits0,zero new owned warnings/errors,zero inherited regressions,695 actual objects and566 unchanged warm objects. Original inherited warnings remain certification-policy debt. Native archive B32CC340F54A682CE0905E9923CD03A8CB0A97CD7E02C4A00FE4E5CEC415D782 is39705754 bytes in two verified copies. Full105's one-time metadata probe is native0 with no failure and344/695 preserved. Trace archive7B46D80B6D45307AC44DDE361E84A47D15297A009557D3F40111C6BFC47151B9 is10192462 bytes in two copies; dedicated02 is independently TERMINATED. Both graphs qualify257/89 roots,8269 exact type-DAG nodes,216 consumed project modules,2762 external constant boundaries and zero unresolved. Historical transport/resource failures and natural pre-custody guest shutdown remain preserved; no compiler or successful probe was replayed.
All340 Full103 source bodies and8260 shared native types/type/proof/union-edge contexts retain exact source/compiler/package/core/cache/configuration identity. All36 actual prior terminal/report/raw/context/source receipts are reverified, including the three Full103 reviews over13 fresh spectral bodies and the earlier33 reports. Per-lens full340 body coverage is identity-eligible; no fresh344-body rereading or cold-checkout/source-object replay is claimed. Complete344 project bodies and411 external-module bodies are available and pinned; availability is not semantic review. Read every supplied complete body, all declarations/Checks in the four fresh current files, and full integration. The packet preserves88 complete parent integration sources plus four fresh sources and all36 report texts unabridged. Distinguish inspected fresh bodies from inherited coverage and explicitly identify skipped required material.
The four fresh files are ActualSelectedComplementSourceSizeSpectralApplication, its Checks, ActualFiniteAppendExactImageEnergy, and its Checks. Inspect the actual SourceSize material and dyadic original-consumer wrappers and sourceSize_spectral47_inhabited, which remove only the old hSpectral premise through the universal exact contract inhabitant. Preserve and compare every original independent row, I/copies/U/A/C/T/f/source-height/rank/table/selector/failed-zoom/rank-domain guard. Caller P is the actual P>=mT, not a fixed4m<=P<8m shortcut. Decide whether prior HIGH F1 is discharged for these exact conditional formal interfaces; do not infer source witness availability or runtime from that discharge.
Inspect all exact image/rank/frame append-energy equalities, arbitrary invariant real F, unconditional append, i<=c+s, empty/nonempty fibres and positive denominator boundaries. The Full104 error and four owned warnings were repaired only by removing an opposite-direction symm, replacing two proof-valued letI bindings with let, and dropping unreachable ring after field_simp; all declaration headers/hypotheses/targets are unchanged and no linter was disabled. Kernel evidence is now present; assess mathematical normalization and applicability from the complete statements. Distinguish explicit native count-ratio energy laws from an exact s-factor eigenvalue product, G/Phi, restricted-adjoint and cross-level identities, which remain argument-level and untranslated. No complex-general manuscript equality or upstream port acceptance is claimed.
Review the entire actual SourceSize/HC46/dyadic and selected-leaf integration, prior spectral character pairing/tail-zero/orbits/counting/guarded weaker+3 contract, and exact normalization. The complete mathematical argument is supplied below. Check zero width/rank/deficient/image/empty boundaries, paired inverses, transpose orientation and natural-to-real conversions. Do not substitute uniform/rank-one noise, a smaller source/star family or a weaker conditional helper for an original obligation.
Retain unresolved numeric NO/hfail/e/scalar, actual independent source/selection/global-table witness, joint arity/source/star/robust8S/pre-draw/sampling/encoded reduction/runtime/learning, exact upstream transport, bootstrap/source-object replay, inherited warning certification and final provider/citation/BibTeX/TeX/PDF/manuscript gates. R14 remains HIGH. Conditional native integration and classical existence do not prove hardness, algorithms, runtime or unconditional sources. Classical append/Fourier/counting reconstruction carries no novelty or priority claim; MZ24 AppendixA13 supports a weaker bound, with exact identities reconstructed separately. No overall GO or publication acceptance is requested.
No tools,writes,Lean/Lake or subagents. Give declaration-specific severity,evidence,disposition and actions, and separate soundness/native translation/conditional integration/overall readiness. Any skipped required fresh body or unresolved HIGH bars overall GO. End with remaining to-do list.
'''
    pieces = [header.encode()]
    marker = json.loads((ROOT.parent/'launch-once.json').read_bytes())
    native = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    native_report = json.loads(native.read_bytes())
    assert native_report['full105_expanded_native_gates_green']
    for label, path in [('CURRENT QUALIFIED NATIVE', native),
                        ('CURRENT QUALIFIED TRACE', BASE/'qualification-summary.json'),
                        ('CURRENT REUSE AUDIT', BASE/'prior-review-reuse-audit.json'),
                        ('CURRENT PREPARED FULL257/FOCUSED89 TOOLING', ROOT.parent/'consumption-preparation-v1-dag/readiness.json')]:
        pieces.append(('\n'+label+' SHA256 '+digest(path)+'\n').encode()+path.read_bytes())
    argument = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp/actual-append-spectral-image-fibre-argument-2026-10-09.md')
    pieces.append(('\nCOMPLETE CRITICAL ARGUMENT SHA256 '+digest(argument)+'\n').encode()+argument.read_bytes())
    for row in reuse['reports']:
        receipt_path = Path(row['path'])
        assert digest(receipt_path) == row['receipt_sha256']
        report = receipt_path.with_suffix('.md')
        assert digest(report) == row['report_sha256']
        pieces.append(('\nCOMPLETE PRESERVED REPORT '+row['folder']+' '+row['lens']+' SHA256 '+digest(report)+'\n').encode()+report.read_bytes())
    for row in rows:
        path = Path(row['source_root'])/row['path']
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
        pieces.append(('\n=== COMPLETE FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+path.read_bytes()+b'\n=== END COMPLETE FILE ===\n')
    text = b''.join(pieces)
    if len(text) >= 2000000:
        raise RuntimeError('Do not truncate required bodies or reports; split complete review packets')
    destination = BASE/'material-integration-v3'
    destination.mkdir()
    output = destination/'integration.txt'
    output.open('xb').write(text)
    result = dict(schema='full105-full344-full257-conditional-material-integration-v3',
        required_lenses=LENSES, packets=[dict(path=str(output), sha256=digest(output), bytes=len(text), files=rows)],
        parent_packet_sha256=packet['sha256'], source_index_sha256=digest(BASE/'review-sources/source-index.json'),
        prior_review_reuse_sha256=digest(BASE/'prior-review-reuse-audit.json'),
        prior_complete_project_bodies_identity_eligible=340, fresh_complete_project_bodies=4,
        complete_supplied_bodies=92, complete_supplied_project_bodies=66,
        all36_prior_report_texts_unabridged=True, roots=257, focused=89, source_scope=344,
        qualified_trace_summary_sha256=digest(BASE/'qualification-summary.json'),
        actual_provider_context_fit_verified=False, accepted=False, full_goal_complete=False)
    (destination/'manifest.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(bytes=len(text), complete_bodies=92, fresh_bodies=4,
        sha256=digest(output), prior_reports=36, accepted=False)))


if __name__ == '__main__':
    main()
