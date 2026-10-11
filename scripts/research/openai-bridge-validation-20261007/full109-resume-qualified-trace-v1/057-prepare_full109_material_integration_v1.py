"""Freeze complete cross-level bodies, actual trace, and all45 prior reports."""
import hashlib
import json
from pathlib import Path
from audit_full109_prior_review_reuse_v1 import BASE, PARENT, HERE, LENSES, FRESH, ROOT
from custody_checks import digest


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    reuse = read(BASE/'prior-review-reuse-audit.json')
    assert reuse['all346_per_lens_prior_body_coverage_identity_eligible'] and len(reuse['reports']) == 45
    assert reuse['fresh_complete_bodies'] == FRESH
    index_path = BASE/'review-sources/source-index.json'
    assert digest(index_path) == reuse['new_source_index_sha256']
    index = read(index_path)
    assert index['project_body_count'] == 348 and len(index['roots']) == 261
    current = {r['path']:r for r in index['project_bodies']}
    parent = read(PARENT/'material-integration-v4/manifest.json')
    originals = {}
    for packet in parent['packets']:
        assert digest(packet['path']) == packet['sha256']
        for row in packet['files']:
            if row['path'] in originals:
                assert row == originals[row['path']]
            originals[row['path']] = row
    assert len(originals) == 98
    rows = []
    for row in originals.values():
        row = dict(row)
        if row['source_kind'] == 'project':
            assert current[row['path']]['sha256'] == row['sha256']
            row['source_root'] = str(BASE/'review-sources')
        rows.append(row)
    for rel in FRESH:
        rows.append(dict(current[rel], source_kind='project', source_root=str(BASE/'review-sources')))
    old_boundaries = read(PARENT/'type-dag-qualification.json')['external_boundaries']
    new_boundaries = read(BASE/'type-dag-qualification.json')['external_boundaries']
    new_constants = sorted(set(new_boundaries)-set(old_boundaries))
    source_rows = {r['constant']:r['source'] for r in index['external_boundaries']}
    present = {r['path'] for r in rows}
    for name in new_constants:
        source = source_rows[name]
        if source['packet_path'] not in present:
            rows.append(dict(path=source['packet_path'], sha256=source['sha256'], bytes=source['bytes'],
                             source_kind='external', source_root=str(BASE/'review-sources'), complete_body=True))
            present.add(source['packet_path'])
    assert len(rows) == len({r['path'] for r in rows})
    summary = read(BASE/'qualification-summary.json')
    assert summary['structural_trace_qualification'] and not any(summary['unresolved_by_graph'].values())
    header = '''FULL109 FULL348/FULL261/FOCUSED93 CROSS-LEVEL MATERIAL INTEGRATION REVIEW.
Current qualified evidence below supersedes historical candidate banners and historical flags. Full109 native GREEN is separate from semantic acceptance. All346 parent source bodies and8298 shared native type/proof dependency nodes are unchanged. All45 prior original reports are revalidated and supplied unabridged. This permits unchanged per-lens body coverage reuse, not a claim of fresh348-body rereading.
Fresh required complete bodies are ActualAppendProductCrossLevelIdentity.lean and its Checks. Read every declaration/proof and the complete critical argument. Check the exact real same-function Gram identity for original unrestricted append and carrier-specific normalized means. Retain i<=c+s, arbitrary real F and its all-matrix paired-inverse right invariance. On i=j consume the native/reviewed s-factor exact product-energy law; on i!=j consume actual append Fourier rank orthogonality. Inspect i>c zero factors, s=0, i=0, zero dimensions, empty support, and absence of an unnecessary j bound. Preserve the exact if-then-else conclusion; no weaker inequality or changed input carrier. Full109 only replaces deprecated if_pos/if_neg aliases in the unaccepted Full108 candidate; no warning suppression or baseline expansion occurred.
Review integration into actual selected-leaf, SourceSize/HC46/dyadic and material callers under their exact prior hypotheses. Separate sound/native conditional real cross-level acceptance from overall manuscript readiness. This theorem does not prove G/Phi composition, independent matrix sampling law, pointwise operator eigenrelation, restricted adjoint, arbitrary two-function or complex extension. It supplies no independent source/selection/global-table/star/robust8S/pre-draw/sampler/encoded reduction/runtime/learning witness. Numeric NO/hfail/scalar/source-height fidelity, exact upstream transport/postobjects, fresh source-object replay, inherited-warning certification, final provider/novelty/citation/manuscript gates and R14 HIGH remain.
Read all supplied complete files and all45 prior reports. Across packets the complete source union is preserved without truncation; both fresh bodies and all arguments/evidence/reports occur in every packet. Each lens must cover every packet before integration acceptance. Report every skip, exact hypotheses, declaration-specific severity, evidence and disposition. Tools, writes, Lean/Lake and subagents are disabled. End with a remaining to-do list. Do not grant overall GO while any required proof or HIGH finding remains.
'''
    pieces = [header.encode()]
    marker = read(ROOT.parent/'launch-once.json')
    native = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    assert read(native)['full109_expanded_native_gates_green']
    evidence = [native, BASE/'qualification-summary.json', BASE/'prior-review-reuse-audit.json',
                ROOT.parent/'consumption-preparation-v1-dag/readiness.json',
                HERE/'full107-material-integration-reports-v4/root-reconciliation-v1.json',
                Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp/actual-append-spectral-image-fibre-argument-2026-10-09.md'),
                HERE/'frame-product-duality-candidate-v1/argument.md',
                HERE/'append-product-crosslevel-warning-repair-candidate-v1/argument.md',
                HERE/'append-product-crosslevel-warning-repair-candidate-v1/derivation.json']
    for path in evidence:
        pieces.append(('\nCOMPLETE EVIDENCE/ARGUMENT '+str(path)+' SHA256 '+digest(path)+'\n').encode()+path.read_bytes())
    for row in reuse['reports']:
        receipt = Path(row['path'])
        report = receipt.with_suffix('.md')
        assert digest(receipt) == row['receipt_sha256'] and digest(report) == row['report_sha256']
        pieces.append(('\nCOMPLETE PRESERVED REPORT '+str(report)+' SHA256 '+digest(report)+'\n').encode()+report.read_bytes())
    prefix = b''.join(pieces)
    sections = {}
    for row in rows:
        path = Path(row['source_root'])/row['path']
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
        sections[row['path']] = ('\n=== COMPLETE FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+path.read_bytes()+b'\n=== END COMPLETE FILE ===\n'
    fresh = [row for row in rows if row['path'] in FRESH]
    assert len(fresh) == 2
    group_count = 2
    while True:
        groups = [[] for _ in range(group_count)]
        sizes = [len(prefix)+sum(len(sections[row['path']]) for row in fresh)]*group_count
        for row in sorted((r for r in rows if r['path'] not in FRESH), key=lambda r:-len(sections[r['path']])):
            number = sizes.index(min(sizes))
            groups[number].append(row)
            sizes[number] += len(sections[row['path']])
        if max(sizes) < 1550000:
            break
        group_count += 1
        assert group_count <= len(rows)-2, 'Whole-file/context split cannot fit; no truncation permitted'
    destination = BASE/'material-integration-v1'
    destination.mkdir()
    packets = []
    for number, group in enumerate(groups, 1):
        selected = fresh+group
        notice = f'\nCURRENT PACKET {number} OF {group_count}; complete union {len(rows)} files. Actual provider context fit remains pending.\n'.encode()
        text = prefix+notice+b''.join(sections[row['path']] for row in selected)
        output = destination/f'integration-{number:02d}.txt'
        output.open('xb').write(text)
        packets.append(dict(path=str(output), sha256=digest(output), bytes=len(text), files=selected))
    assert {r['path'] for p in packets for r in p['files']} == set(sections)
    result = dict(schema='full109-full348-full261-crosslevel-material-integration-v1', required_lenses=LENSES,
                  packets=packets, complete_file_union_preserved=len(rows), all45_prior_reports_unabridged=True,
                  fresh_two_complete_bodies_in_each_packet=True, source_scope=348, roots=261, focused=93,
                  prior_complete_project_bodies_identity_eligible=346, new_external_constants=new_constants,
                  common_prefix_sha256=hashlib.sha256(prefix).hexdigest().upper(),
                  source_index_sha256=digest(index_path), prior_review_reuse_sha256=digest(BASE/'prior-review-reuse-audit.json'),
                  actual_provider_context_fit_verified=False, accepted=False, full_goal_complete=False)
    (destination/'manifest.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(packets=len(packets), bytes=[r['bytes'] for r in packets], complete_union=len(rows), accepted=False)))


if __name__ == '__main__':
    main()
