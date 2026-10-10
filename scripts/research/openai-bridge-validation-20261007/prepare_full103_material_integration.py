"""Freeze complete changed bodies and unabridged prior review evidence."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full103_prior_review_reuse import BASE, PARENT, HERE, LENSES
from full103_consumption_v2_controller import ROOT


def main():
    reuse = json.loads((BASE/'prior-review-reuse-audit.json').read_bytes())
    assert reuse['all327_per_lens_prior_body_coverage_identity_eligible']
    assert len(reuse['fresh_complete_bodies']) == 13 and len(reuse['reports']) == 33
    index = json.loads((BASE/'review-sources/source-index.json').read_bytes())
    assert index['project_body_count'] == 340 and len(index['roots']) == 251
    assert digest(BASE/'review-sources/source-index.json') == reuse['new_source_index_sha256']
    current = {row['path']:row for row in index['project_bodies']}
    parent = json.loads((PARENT/'material-integration-v1/manifest.json').read_bytes())
    packet = parent['packets'][0]
    assert digest(packet['path']) == packet['sha256'] and len(packet['files']) == 75
    rows = []
    for row in packet['files']:
        row = dict(row)
        if row['source_kind'] == 'project':
            assert current[row['path']]['sha256'] == row['sha256']
            row['source_root'] = str(BASE/'review-sources')
        rows.append(row)
    for rel in reuse['fresh_complete_bodies']:
        rows.append(dict(current[rel], source_kind='project', source_root=str(BASE/'review-sources')))
    assert len(rows) == len({row['path'] for row in rows}) == 88
    assert sum(row['source_kind'] == 'project' for row in rows) == 62
    header = '''FULL103 FULL340/FULL251/FOCUSED83 CONDITIONAL INTEGRATION REVIEW.
These current instructions and verified scope supersede historical status banners and instructions in the preserved reports below. Full103 has qualified native GREEN: all340 sources,251 required standard-axiom profiles,all seven stages0,zero owned warning headers and zero inherited regressions,687 actual compiled objects and566 unchanged warm objects. The sole full251/focused83 GCP trace is native0 and preserves340/687. Exact10,162,992-byte two-copy custody is B066026546FC4497D32EBD5583FFE7655F7979BAA7702CB1498BFCB420F44515; dedicated02 is independently TERMINATED. Original SCP controller failure, partial bytes and local historical192/24 postprocessor failure remain preserved. The successful trace was not repeated. Local qualification-v3 changes only normalized-text cardinality guards192->251/24->83 and graph labels; frozen probe/tooling and type-DAG algorithms remain unchanged. Both graphs have zero unresolved,8260 exact type-DAG nodes,214 project modules and2762 external constant boundaries.
All327 parent source bodies and8084 shared native constant types/type/proof/union edges retain exact source/compiler/package/core/cache/configuration identity. Thirty-three actual prior terminal/context/report/source receipts have been reverified. Per-lens inherited full327 body coverage is eligible for identity reuse; it is not a claim of fresh340-body rereading or fresh-checkout source-object replay. The complete340 project and411 external-module source corpus is indexed and preserved. Its availability is not semantic review. Read every supplied complete body, all declarations in the13 new/repaired spectral-family files, and full conditional integration. The packet contains all75 complete parent integration sources plus those13 current complete sources, with all33 prior report texts unabridged. Identify inspected/skipped supplied bodies and separate fresh coverage from inherited reuse.
The eleven recovered spectral modules and legacy selected-leaf application are now kernel-verified in these exact current bytes. The warnings were repaired without theorem-header changes. Independently assess actual character pairing/tail-zero, same-image orbit invariance, surjection/independent-row counting, empty fibres, frame counts and normalization, per-image/global retained energy,dyadic decay and the guarded weaker+3 Spectral47 contract. Check every zero-width/rank/deficient/image/empty boundary, paired inverses, transpose orientation and natural-to-real conversion. The declared universal contract inhabitant and legacy selected-leaf spectral application have native evidence; verify the exact statement and all hypotheses rather than upgrading the flag alone to mathematics or manuscript acceptance.
Assess the actual full SourceSize/HC46/dyadic integration with independent source rows versus leaf arity and exact I/copies/U/A/C/T/f/source-height/rank/harness/table/selector/failed-zoom guards. Full103 does not remove the spectral premise from the actual SourceSize/dyadic consumers: Full104's separately reviewed four-file344/257 candidate is frozen/unlaunched and outside this native scope. No eigenvalue product/G-Phi/restricted-adjoint/cross-level native equality is claimed. The complete exact operator argument below is a reviewed mathematical route, with those translations still pending. Do not substitute uniform/rank-one noise, a smaller source/star family, a fixed exponent below required mT, or a conditional helper for an original obligation.
Preserve each prior open finding. Useful numeric NO/hfail/e,actual independent source/selection/global-table witness,joint source arity,source/star/robust8S/pre-draw/sampling/encoded reduction/runtime/learning,exact upstream transports,fresh checkout/object replay,inherited warning certification and final provider/citation/PDF/manuscript acceptance remain open. R14 remains HIGH. Neither conditional native integration nor finite classical existence proves hardness, actual algorithms, runtime or unconditional source availability. Classical append/Fourier/counting reconstructions carry no novelty or priority claim. MZ24 AppendixA13 supports a weaker bound; exact identities are separately reconstructed, not falsely cited as its literal statement. No overall GO or manuscript/publication acceptance is requested.
No tools,writes,Lean/Lake or subagents. Give declaration-specific severity,evidence,disposition and actions. Distinguish mathematical soundness, native translation, conditional integration and overall readiness. Any skipped required fresh body or unresolved HIGH bars overall GO. End with remaining to-do list.
'''
    pieces = [header.encode()]
    marker = json.loads((ROOT.parent/'launch-once.json').read_bytes())
    native = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    native_report = json.loads(native.read_bytes())
    assert native_report['full103_expanded_native_gates_green']
    for label, path in [('CURRENT QUALIFIED NATIVE', native),
                        ('CURRENT QUALIFIED TRACE', BASE/'qualification-summary.json'),
                        ('CURRENT REUSE AUDIT', BASE/'prior-review-reuse-audit.json'),
                        ('LOCAL SCOPE REPAIR', HERE/'full103-trace-postprocess-scope-derivation-v3.json')]:
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
    if len(text) >= 1800000:
        raise RuntimeError('Do not truncate required bodies or reports; split complete review packets')
    destination = BASE/'material-integration-v3'
    destination.mkdir()
    output = destination/'integration.txt'
    output.open('xb').write(text)
    result = dict(schema='full103-full340-full251-conditional-material-integration-v3',
        required_lenses=LENSES, packets=[dict(path=str(output), sha256=digest(output), bytes=len(text), files=rows)],
        parent_packet_sha256=packet['sha256'], source_index_sha256=digest(BASE/'review-sources/source-index.json'),
        prior_review_reuse_sha256=digest(BASE/'prior-review-reuse-audit.json'),
        prior_complete_project_bodies_identity_eligible=327, fresh_complete_project_bodies=13,
        complete_supplied_bodies=88, complete_supplied_project_bodies=62,
        all33_prior_report_texts_unabridged=True, roots=251, focused=83, source_scope=340,
        qualified_trace_summary_sha256=digest(BASE/'qualification-summary.json'),
        actual_provider_context_fit_verified=False, accepted=False, full_goal_complete=False)
    (destination/'manifest.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(bytes=len(text), complete_bodies=88, fresh_bodies=13,
        sha256=digest(output), prior_reports=33, accepted=False)))


if __name__ == '__main__':
    main()
