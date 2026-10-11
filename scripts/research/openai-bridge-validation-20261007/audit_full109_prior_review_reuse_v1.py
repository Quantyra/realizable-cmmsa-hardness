"""Require complete parent review custody and unchanged native dependency context."""
import hashlib
import json
from pathlib import Path
import sys
import tarfile
from audit_full107_prior_review_reuse import parent_review, LENSES
from audit_full100_prior_review_reuse import report
from custody_checks import digest
from full109_consumption_v3_controller import ROOT

HERE = Path(__file__).parent
BASE = ROOT/'qualification'
PARENT = ROOT.parent.parent/'full107-exact-product-energy-repair-resource02/consumption-v3/qualification'
FRESH = ['lean/PvNP/RealizableHardness/ActualAppendProductCrossLevelIdentity.lean',
         'lean/PvNP/RealizableHardness/ActualAppendProductCrossLevelIdentityChecks.lean']


def read(path):
    return json.loads(Path(path).read_bytes())


def main(parent_only=False):
    old344, reports, _ = parent_review()
    prior_path = PARENT/'prior-review-reuse-audit.json'
    assert digest(prior_path) == 'B66855918F44FE8AE4B6354C581B324AD59C85FE064F08C8728B1B76DD32EF05'
    prior = read(prior_path)
    assert prior['all344_per_lens_prior_body_coverage_identity_eligible']
    assert set(prior['unchanged_prior_complete_bodies']) == set(old344)
    assert len(reports) == len(prior['reports']) == 39
    assert {r['receipt_sha256'] for r in reports} == {r['receipt_sha256'] for r in prior['reports']}
    index_path = PARENT/'review-sources/source-index.json'
    assert digest(index_path) == prior['new_source_index_sha256']
    assert digest(PARENT/'graphs/validated-graphs.json') == prior['new_graph_sha256']
    old = {r['path']:r for r in read(index_path)['project_bodies']}
    assert len(old) == 346
    for rel, row in old.items():
        source = PARENT/'review-sources'/rel
        assert digest(source) == row['sha256'] and source.stat().st_size == row['bytes']
        if rel in old344:
            assert (row['sha256'],row['bytes']) == (old344[rel]['sha256'],old344[rel]['bytes'])
    settlement_path = HERE/'full107-material-integration-reports-v4/root-reconciliation-v1.json'
    assert digest(settlement_path) == '0BF97A645869BB8974A726693FD6521B057686EF0DAB78BA0E665762D89D29E4'
    settlement = read(settlement_path)
    assert settlement['reports_read_in_full'] and settlement['conditional_product_energy_milestone_accepted']
    assert not settlement['overall_accepted'] and len(settlement['reports']) == 6
    for lens in LENSES:
        covered = set(old344)
        for number in (1, 2):
            path, receipt = report('full107-material-integration-reports-v4', lens, number)
            expected = next(r for r in settlement['reports'] if (r['lens'],r['packet']) == (lens,number))
            assert digest(path) == expected['receipt_sha256']
            assert receipt['report_sha256'] == expected['report_sha256']
            assert receipt['raw_stdout_sha256'] == expected['raw_stdout_sha256']
            assert receipt['num_turns'] == 1 and receipt['subagents_spawned'] == 0
            assert receipt['reported_model'] == 'claude-opus-5-5[1m]'
            assert receipt['input_tokens_including_cache']+receipt['output_tokens'] <= receipt['context_window'] == 1000000
            assert expected['fresh_two_files_all_declarations_inspected'] and expected['required_fresh_bodies_skipped'] == 0
            raw = read(receipt['raw_stdout_path'])
            assert not raw['is_error'] and raw['subagent_stats']['spawned'] == 0
            for row in receipt['supplied_complete_files']:
                if row['source_kind'] == 'project':
                    assert row['sha256'] == old[row['path']]['sha256']
                    covered.add(row['path'])
            reports.append(dict(path=str(path), lens=lens, packet=number, receipt_sha256=digest(path),
                                report_sha256=receipt['report_sha256'], raw_stdout_sha256=receipt['raw_stdout_sha256']))
        assert covered == set(old)
    assert len(reports) == 45
    resource = ROOT.parent
    binding = read(resource/'resource-binding.json')
    archive_path = resource/'input-archive.tar.gz'
    manifest_path = resource/'capture-manifest.json'
    assert digest(archive_path) == binding['files']['input-archive.tar.gz']
    assert digest(manifest_path) == binding['files']['capture-manifest.json']
    manifest = read(manifest_path)
    captured = manifest['project_sources']
    assert len(captured) == 348 and sorted(set(captured)-set(old)) == FRESH
    with tarfile.open(archive_path) as archive:
        for rel, row in captured.items():
            data = archive.extractfile(rel).read()
            assert hashlib.sha256(data).hexdigest().upper() == row['sha256'] and len(data) == row['bytes']
            if rel in old:
                assert (row['sha256'],row['bytes']) == (old[rel]['sha256'],old[rel]['bytes'])
    value = dict(schema='full109-prior346-body-and45-review-identity-v1',
                 parent_source_index_sha256=digest(index_path), parent_reuse_audit_sha256=digest(prior_path),
                 parent_settlement_sha256=digest(settlement_path), reports=reports,
                 current_capture_manifest_sha256=digest(manifest_path),
                 all348_capture_body_hashes_verified=True, unchanged346_capture_body_hashes_verified=True,
                 fresh_complete_bodies=FRESH, accepted=False, full_goal_complete=False,
                 fresh_two_body_and_full_integration_review_required=True,
                 prior_findings_and_HIGH_residues_retained=True,
                 all346_per_lens_prior_body_coverage_identity_eligible=False)
    target = HERE/'full109-parent-review-custody-preparation-v1.json'
    if not parent_only:
        new_index = read(BASE/'review-sources/source-index.json')
        new = {r['path']:r for r in new_index['project_bodies']}
        assert len(new) == 348 and set(new) == set(captured)
        for rel, row in new.items():
            assert (row['sha256'],row['bytes']) == (captured[rel]['sha256'],captured[rel]['bytes'])
            path = BASE/'review-sources'/rel
            assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
        graphs = [read(folder/'graphs/validated-graphs.json') for folder in (PARENT, BASE)]
        dags = [read(folder/'type-dag-qualification.json')['type_dag_sha256'] for folder in (PARENT, BASE)]
        assert len(graphs[0]['nodes']) == 8298
        for name, row in graphs[0]['nodes'].items():
            other = graphs[1]['nodes'][name]
            assert dags[0][name] == dags[1][name]
            for field in ['kind','module','project','body_available','body_unresolved','ownership_unresolved']:
                assert row[field] == other[field]
            for field in ['type_edges','proof_edges','union_edges']:
                assert set(row[field]) == set(other[field])
        parent_manifest = read(PARENT.parent.parent/'capture-manifest.json')
        for field in ['cache_provenance','configs']:
            assert manifest[field] == parent_manifest[field]
        assert graphs[1]['graphs']['exact261-native']['roots'] == manifest['requested_axioms']
        assert len(graphs[1]['graphs']['focused-ninety-three-consumer']['roots']) == 93
        summary = read(BASE/'qualification-summary.json')
        assert summary['structural_trace_qualification'] and not any(summary['unresolved_by_graph'].values())
        value.update(all346_per_lens_prior_body_coverage_identity_eligible=True,
                     shared_native_types_and_body_dependencies_unchanged=8298,
                     compiler_package_core_cache_configuration_preserved=True,
                     new_source_index_sha256=digest(BASE/'review-sources/source-index.json'),
                     new_graph_sha256=digest(BASE/'graphs/validated-graphs.json'))
        target = BASE/'prior-review-reuse-audit.json'
    with target.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(parent_bodies=346, original_reports=45, capture_bodies=348,
                          actual_trace_context_verified=not parent_only, accepted=False)))


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--parent-only'])
    main(sys.argv[1:] == ['--parent-only'])
