"""Root settlement after full reading of six reports; exact conditional Gram scope only."""
import difflib
import json
from pathlib import Path
import re
import tarfile
from audit_full109_prior_review_reuse_v1 import BASE, PARENT, HERE, FRESH, LENSES, ROOT
from custody_checks import digest


def read(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            assert key not in result, 'Duplicate JSON key: '+key
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique)


def save(path, value):
    path.open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')


def main():
    folder = HERE / 'full109-material-integration-reports-v1'
    manifest = read(BASE / 'material-integration-v1/manifest.json')
    assert manifest['required_lenses'] == LENSES and len(manifest['packets']) == 2
    complete = {row['path']: row for packet in manifest['packets'] for row in packet['files']}
    assert len(complete) == manifest['complete_file_union_preserved'] == 100
    reports = []
    for lens in LENSES:
        covered = set()
        for number, packet in enumerate(manifest['packets'], 1):
            path = folder / f'{lens}-{number:02d}.json'
            receipt = read(path)
            assert receipt['native_exit'] == 0 and receipt['actual_packet_context_fit']
            assert receipt['num_turns'] == 1 and receipt['subagents_spawned'] == 0
            assert receipt['reported_model'] == 'claude-opus-5-5[1m]'
            assert receipt['input_tokens_including_cache'] + receipt['output_tokens'] <= receipt['context_window'] == 1000000
            assert receipt['supplied_complete_files'] == packet['files']
            assert receipt['packet_sha256'] == packet['sha256'] == digest(packet['path'])
            assert digest(path.with_suffix('.md')) == receipt['report_sha256']
            assert digest(receipt['raw_stdout_path']) == receipt['raw_stdout_sha256']
            raw = read(receipt['raw_stdout_path'])
            assert not raw['is_error'] and raw['subagent_stats']['spawned'] == 0
            assert raw['modelUsage']['claude-opus-5-5[1m]']['webSearchRequests'] == 0
            assert raw['terminal_reason'] == 'completed' and raw['stop_reason'] == 'end_turn'
            assert set(FRESH) <= {row['path'] for row in packet['files']}
            for row in packet['files']:
                source = Path(row['source_root']) / row['path']
                assert digest(source) == row['sha256'] == complete[row['path']]['sha256']
                assert source.stat().st_size == row['bytes']
                covered.add(row['path'])
            reports.append(dict(lens=lens, packet=number, receipt_sha256=digest(path),
                report_sha256=receipt['report_sha256'], raw_stdout_sha256=receipt['raw_stdout_sha256'],
                input_tokens=receipt['input_tokens_including_cache'], output_tokens=receipt['output_tokens'],
                actual_context_fit=True, fresh_two_files_all_declarations_inspected=True,
                required_fresh_bodies_skipped=0, conditional_verdict='GO-WITH-NOTES',
                overall_verdict='NO-GO; R14 HIGH and remaining gates open'))
        assert covered == set(complete)
    reuse = read(BASE / 'prior-review-reuse-audit.json')
    assert reuse['all346_per_lens_prior_body_coverage_identity_eligible'] and len(reuse['reports']) == 45
    source_index = read(BASE / 'review-sources/source-index.json')
    assert source_index['selection_complete_for_native261_and_entire_capture']
    assert source_index['project_body_count'] == 348
    source = BASE / 'review-sources' / FRESH[0]
    old_source = HERE / 'append-product-crosslevel-candidate-v1/ActualAppendProductCrossLevelIdentity.lean'
    old, new = old_source.read_bytes(), source.read_bytes()
    assert digest(old_source) == 'B3F1C4F561D310F58B59BE69F7BA4EFE6E6CB883A1AEE61AAF5AFE0CCFD5FE7B'
    assert digest(source) == 'BB738BC924AD7F06141A6904E8A043F1A8023863B293087D269D421EF76CCE90'
    assert old.count(b'if_pos') == old.count(b'if_neg') == 1
    assert old.replace(b'if_pos', b'ite_eq_left').replace(b'if_neg', b'ite_eq_right') == new
    assert re.findall(r'^theorem (\w+)', new.decode('utf-8'), re.M) == ['append_rank_cross_level_gram_eq_product']
    old_dag, new_dag = [read(root / 'type-dag-qualification.json') for root in (PARENT, BASE)]
    names = sorted(set(new_dag['type_dag_sha256']) - set(old_dag['type_dag_sha256']))
    assert names == ['PvNP.RealizableHardness.ActualAppendProductCrossLevelIdentity.append_rank_cross_level_gram_eq_product']
    assert not (set(old_dag['type_dag_sha256']) - set(new_dag['type_dag_sha256']))
    assert old_dag['external_boundaries'] == new_dag['external_boundaries']
    resource = ROOT.parent
    marker = read(resource / 'launch-once.json')
    custody = read(Path(marker['preflight']) / 'terminal-custody.json')['custody']
    assert digest(custody['repository_path']) == custody['remote_sha256'] == 'BD8EC70F9A138EBB5C3AC8E52B7732CF7CFE3D3E5C9B9F8CB3FB16FE37F21154'
    capture = read(resource / 'capture-manifest.json')
    with tarfile.open(custody['repository_path']) as archive:
        objects = json.load(archive.extractfile('object-after.json'))
        cache = json.load(archive.extractfile('verified-cache-provenance.json'))
    assert cache == capture['cache_provenance']
    warm = cache['objects']
    assert len(warm) == 566 and len(objects) == 703
    assert all(objects.get(name) == pin for name, pin in warm.items())
    extra = {name: pin for name, pin in objects.items() if name not in warm}
    assert len(extra) == 137
    addendum = dict(schema='full109-root-alias-trace-and-object-identity-addendum-v1',
        original_source_sha256=digest(old_source), current_source_sha256=digest(source),
        exact_two_alias_replacement_verified=True, original_source=old.decode('utf-8'),
        current_source=new.decode('utf-8'),
        full_diff=''.join(difflib.unified_diff(old.decode('utf-8').splitlines(True), new.decode('utf-8').splitlines(True), fromfile='Full108', tofile='Full109')),
        added_native_nodes={name:new_dag['type_dag_sha256'][name] for name in names},
        external_boundary_dictionary_unchanged=True,
        warm_objects_unchanged=566, complete_post_object_inventory=703,
        objects_additional_to_warm_baseline=extra,
        count_explanation='566 is the unchanged warm subset of the complete 703-entry post-run inventory; 137 entries lie outside that subset. These are object counts, not source counts.',
        current_reuse_audit_duplicate_json_keys=False,
        supplied_to_original_reviewers=False, new_semantic_acceptance=False, fresh_checkout_replay=False)
    save(folder / 'identity-addendum-v1.json', addendum)
    result = dict(schema='full109-independent-six-report-root-settlement-v1', reports=reports,
        reports_read_in_full=True, complete_supplied_file_union_per_lens=100,
        identity_reuse_project_bodies=346, fresh_project_bodies=2,
        all100_bodies_freshly_reread_by_every_reviewer=False,
        reused_parent_bodies_and_reviewed_critical_interfaces_distinguished=True,
        exact_real_same_function_crosslevel_gram_native_and_reviewed=True,
        conditional_crosslevel_milestone_accepted=True,
        theorem_guard='i <= c+s; arbitrary real F invariant under all paired-inverse right actions; no j guard',
        material_rhs_tightened=False, new_source_or_sampler_witness=False,
        G_Phi_eigenrelation_adjoint_two_function_complex_translation_closed=False,
        historical_capture_flags_preserved=True,
        report_wording_corrections=[
            'The product-energy identity remains zero outside rank support; the ratio formula needing hi does not make hi mathematically essential to this zero-energy case. The stated guard is retained.',
            'Current source-index proves complete selection of 348 captured review bodies; source_selection_complete=false in the earlier qualification summary is historical, distinct from the still-open mathematical source witness.',
            'Current prior-review-reuse-audit.json has no duplicate keys; the complexity packet-1 duplicate-key assertion is not true of this artifact.',
            'Actual provider context fit is established by terminal modelUsage receipts, not reviewer introspection.',
            'Checks source produces declarations/profile output; the preserved authoritative native logs and audits provide the resulting evidence.',
            'Identity-reused parent bodies need not all be freshly re-derived. All required fresh declarations were read in both packets by all three lenses.'
        ],
        identity_addendum_sha256=digest(folder / 'identity-addendum-v1.json'),
        identity_addendum_supplied_to_reviewers=False,
        prior_scope_findings_and_R14_HIGH_retained=True,
        trace=dict(roots=261, focused_roots=93, nodes=8299, exact_type_edge_matches=8299,
                   project_modules=218, external_boundaries=2767, unresolved=0),
        fresh_checkout_replay=False, overall_accepted=False, full_goal_complete=False,
        remaining=[
            'Full110 real/complex G/Phi, eigenrelation, restricted adjoint and two-function Gram native/trace/review qualification',
            'Numeric NO/scalar/useful hfail and explicit source-height floor',
            'Joint source/selection/global-table/star/robust8S/pre-draw/physical sampler witnesses',
            'R14 HIGH encoded reduction/runtime/learning',
            'Exact upstream transports and original post-object audit',
            'Fresh checkout source/object replay and inherited-warning certification decision',
            'Historical headers/flags and legacy spectral-conditional exports in immutable successor only',
            'Final provider/novelty/citations/BibTeX/TeX/PDF/manuscript gates'])
    save(folder / 'root-reconciliation-v1.json', result)
    print(json.dumps(dict(reports=6, all_actual_context_fits=True, conditional_crosslevel_accepted=True,
                         root_sha256=digest(folder / 'root-reconciliation-v1.json'), overall_accepted=False)))


if __name__ == '__main__':
    main()
