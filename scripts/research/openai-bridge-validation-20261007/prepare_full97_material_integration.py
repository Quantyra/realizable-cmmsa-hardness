"""Freeze full-scope integration with complete new bodies and typed identities."""
import hashlib
import json
from pathlib import Path
from prepare_builder02_full97 import OUTPUT

HERE = Path(__file__).parent
BASE = OUTPUT / 'consumption-v1/qualification'
OLD = OUTPUT.parent / 'full95-manuscript-moment-syntax-repair-resource02/consumption-v1/qualification'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    reuse = json.loads((BASE / 'prior-review-reuse-audit.json').read_bytes())
    index = json.loads((BASE / 'review-sources/source-index.json').read_bytes())
    if not reuse['reuse_identity_eligible'] or len(reuse['unchanged_prior_complete_bodies']) != 323 or reuse['shared_native_constant_types_and_edges_unchanged'] != 8069:
        raise RuntimeError('Complete prior source/type/proof reuse required')
    if len(reuse['new_or_changed_complete_bodies']) != 2 or index['project_body_count'] != 325 or len(index['roots']) != 184:
        raise RuntimeError('Full325/full184 current source scope required')
    parent = json.loads((OLD / 'material-integration-v1/manifest.json').read_bytes())
    packet = parent['packets'][0]
    raw = Path(packet['path']).read_bytes()
    if sha(raw) != packet['sha256']:
        raise RuntimeError('Parent complete review packet changed')
    # Keep the historical evidence without pretending its scope or decisions
    # already cover the new declarations. Every supplied source remains whole.
    header = b"""FULL97 COMPLETE TWO-NEW-BODY AND WHOLE CONDITIONAL MATERIAL INTEGRATION REVIEW.
These current instructions supersede every historical FULL95/FULL90 instruction preserved below. Current scope is325 captured project bodies,184 required profiles and exact184/focused16 qualified trace.323 unchanged prior complete bodies have verified per-lens review provenance, identical source/configuration/compiler/package/core context, and8069 unchanged native constant types/type/proof edges. This permits identity reuse; do not claim fresh rereading of absent bodies. The old three-lens verdict is conditional GO-WITH-NOTES, with R14 encoded runtime/reduction still HIGH outside that bounded result. Preserve the old findings and stated remaining scope.
Inspect every supplied complete source, especially BinaryMatrixSameRangeOrbit.lean and SourceSizeContractBridge.lean. The packet also supplies the complete sealed MatrixLiftAffineTarget.lean support and the prior67 complete files (44 project/23 Complexitylib). Explicitly list inspected/skipped bodies and inspect every new declaration. The full325-body and409-external-file corpus is preserved by indexed identities; source availability does not mean every body was newly read.
Audit the generic same-range orbit theorem's full hypotheses, range/codomain restriction, surjectivity, domain-equivalence direction, subtype equality, deficient-map/zero-dimensional cases and actual use of surjective_target_orbit. It currently proves a finite-dimensional binary-module statement; it has not yet proved matrix-action/Fourier/cardinality/append-energy bridges or universal Spectral47. Audit both contract equivalences against the entire retained legacy and SourceSize definitions, including budgets, Boolean/function carrier, normalization, dyadic exponent, all-matrix paired-inverse invariance, source cutoff and every quantified source guard. Kernel definitional equivalence transfers an inhabitant; it does not construct one.
Continue whole conditional material integration: same actual I/copies/U/A/C/T/f, source row count independent of leaf query count, actual SourceSize dimensions, original HC46 inhabitant/application, arbitrary caller dyadic exponent and all existing height/rank/dimension/harness guards. Do not replace the actual append experiment with uniform/rank-one noise, narrow the source/star family, or treat selected upstream native profiles as CMMSA bridges. Generic/source-body selection is distinct from mathematical pre-draw source/selection/global-table obligations.
IMPORTANT TYPED HASH CUSTODY: .lean source SHA values and .olean compiled-object SHA values are separate categories. The current qualified native report has explicit added_source_object_identities. Its legacy added_object_hashes dictionary uses source paths as keys but object digests as values. The preserved Full95 original H1 comparison of these different categories was independently closed by all three addenda. Inspect the supplied mapping and six original/addendum reports; do not reopen a category error or silently reinterpret object hashes as source hashes. Raw reports are historical evidence, not current acceptance.
Universal actual Spectral47, useful numeric NO/hfail/e, joint source/selector/copies/U/A witnesses, source/star/robust8S and pre-draw global table, physical sampler, encoded runtime/reduction/learning, fresh-checkout/warning debt and full novelty/citation/PDF/publication gates remain open. Inherited total warning debt is explicit although owned/regression gates are zero. No new priority/novelty, unconditional material theorem, overall GO or manuscript acceptance follows from this packet. Distinguish native/conditional integration from each remaining mathematical and publication obligation.
No tools, writes, Lean/Lake or subagents. Report declaration-specific severity, evidence, disposition and actions. State conditional integration verdict separately from overall readiness. Any unresolved HIGH or skipped required fresh body bars overall GO. End with remaining to-do list.
"""
    text = header
    for kind, folder_name in [('ORIGINAL', 'full95-material-integration-reports'),
                              ('IDENTITY ADDENDUM', 'full95-material-identity-addendum-reports')]:
        for lens in parent['required_lenses']:
            path = HERE / folder_name / (lens + '-01.md')
            receipt = json.loads(path.with_suffix('.json').read_bytes())
            data = path.read_bytes()
            if sha(data) != receipt['report_sha256'] or receipt['native_exit'] != 0 or not receipt['actual_packet_context_fit']:
                raise RuntimeError('Preserved prior review evidence changed')
            text += ('\nPRESERVED FULL95 ' + kind + ' REPORT ' + lens + ' SHA256 ' + sha(data) + '\n').encode() + data
    marker = json.loads((OUTPUT / 'launch-once.json').read_bytes())
    native = Path(marker['preflight']) / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    for label, path in [
        ('CURRENT QUALIFIED NATIVE REPORT', native),
        ('CURRENT QUALIFIED TRACE', BASE / 'qualification-summary.json'),
        ('EXACT FULL323 BODY AND TYPE/PROOF REUSE AUDIT', BASE / 'prior-review-reuse-audit.json'),
        ('PRESERVED FULL95 TYPED SOURCE/OBJECT CATEGORY SETTLEMENT', OLD / 'source-object-identity-reconciliation-v1.json'),
        ('PRESERVED FULL95 ROOT CONDITIONAL RECONCILIATION', OLD / 'material-review-root-reconciliation-v1.json')]:
        data = path.read_bytes()
        text += ('\n' + label + ' SHA256 ' + sha(data) + '\n').encode() + data
    # Remove the inherited packet's duplicated evidence wrappers by retaining
    # its complete source files, already identified individually in its manifest.
    # Prior Full90 report evidence is supplied separately and without abridgment.
    for folder_name in ['full90-material-review-reports', 'full90-material-integration-reports']:
        for path in sorted((HERE / folder_name).glob('*.md')):
            receipt = json.loads(path.with_suffix('.json').read_bytes())
            data = path.read_bytes()
            if sha(data) != receipt['report_sha256'] or receipt['native_exit'] != 0:
                raise RuntimeError('Full90 historical report changed')
            text += ('\nPRESERVED FULL90 REPORT ' + path.stem + '\n').encode() + data
    rows = list(packet['files'])
    supplied = {r['path'] for r in rows}
    bodies = {r['path']: r for r in index['project_bodies']}
    required = reuse['new_or_changed_complete_bodies'] + ['lean/PvNP/RealizableHardness/MatrixLiftAffineTarget.lean']
    for path in required:
        if path not in supplied:
            rows.append(dict(bodies[path], source_kind='project', source_root=str(BASE / 'review-sources')))
            supplied.add(path)
    for row in rows:
        data = (Path(row['source_root']) / row['path']).read_bytes()
        if len(data) != row['bytes'] or sha(data) != row['sha256']:
            raise RuntimeError('Complete supplied source changed')
        text += ('\n=== COMPLETE FILE ' + row['source_kind'] + ' ' + row['path']
                 + ' SHA256 ' + row['sha256'] + ' ===\n').encode() + data + b'\n=== END COMPLETE FILE ===\n'
    if len(rows) != 70 or sum(r['source_kind'] == 'project' for r in rows) != 47:
        raise RuntimeError('Unexpected whole-file packet body coverage')
    if len(text) >= 1800000:
        raise RuntimeError('Do not truncate; prepare more complete-body packets')
    destination = BASE / 'material-integration-v1'
    destination.mkdir()
    path = destination / 'integration.txt'
    path.write_bytes(text)
    value = dict(schema='full97-full184-two-new-body-conditional-material-integration-v1',
        required_lenses=parent['required_lenses'],
        packets=[dict(path=str(path), sha256=sha(text), bytes=len(text), files=rows)],
        preserved_parent_packet_sha256=packet['sha256'], prior_complete_project_bodies_identity_eligible=323,
        new_complete_project_bodies=2, complete_supplied_bodies=70,
        complete_supplied_project_bodies=47, complete_supplied_Complexitylib_bodies=23,
        sealed_orbit_support_complete_body_included=True, roots=184, focused=16,
        actual_provider_context_fit_verified=False, full_goal_complete=False, accepted=False)
    (destination / 'manifest.json').write_bytes((json.dumps(value, indent=2) + '\n').encode())
    print(json.dumps(dict(bytes=len(text), complete_bodies=70, fresh_bodies=2,
                         sha256=sha(text), accepted=False)))


if __name__ == '__main__':
    main()
