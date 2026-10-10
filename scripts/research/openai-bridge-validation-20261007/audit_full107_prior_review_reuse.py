"""Verify Full105 body/review custody, then require exact Full107 graph identity."""
import json
import hashlib
from pathlib import Path
import sys
import tarfile
from custody_checks import digest
from audit_full100_prior_review_reuse import report
from full107_consumption_v3_controller import ROOT

HERE = Path(__file__).parent
BASE = ROOT/'qualification'
PARENT = ROOT.parent.parent/'full105-actual-consumer-exact-energy-repair-resource02/consumption-v3/qualification'
LENSES = ['proof-adversarial', 'complexity', 'non-claims']
PRIOR_SHA = '754CE52AEDBB0580A78C3986C5B18B87FC6E8D3042A733D37FECD83B4699C990'
SETTLEMENT_SHA = '9042FBDB7C715D96860B6004A91049FB136FFE4E4EE9620F3720C8EF44C8B382'
FRESH = ['lean/PvNP/RealizableHardness/ActualFiniteFrameProductDuality.lean',
         'lean/PvNP/RealizableHardness/ActualFiniteFrameProductDualityChecks.lean']


def read(path):
    return json.loads(Path(path).read_bytes())


def store(path, value):
    data = (json.dumps(value, indent=2)+'\n').encode('utf-8')
    if path.exists():
        assert path.read_bytes() == data, 'Existing audit drift'
    else:
        path.open('xb').write(data)


def parent_review():
    prior_path = PARENT/'prior-review-reuse-audit.json'
    assert digest(prior_path) == PRIOR_SHA
    prior = read(prior_path)
    assert prior['all340_per_lens_prior_body_coverage_identity_eligible']
    assert len(prior['reports']) == 36
    index_path = PARENT/'review-sources/source-index.json'
    assert digest(index_path) == prior['new_source_index_sha256']
    assert digest(PARENT/'graphs/validated-graphs.json') == prior['new_graph_sha256']
    index = read(index_path)
    old = {row['path']: row for row in index['project_bodies']}
    assert len(old) == len(index['project_bodies']) == 344
    for rel, row in old.items():
        path = PARENT/'review-sources'/rel
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    settlement_path = HERE/'full105-material-integration-reports/root-reconciliation-v1.json'
    assert digest(settlement_path) == SETTLEMENT_SHA
    settlement = read(settlement_path)
    assert settlement['reports_read_in_full']
    assert settlement['exact_real_invariant_append_frame_ratio_energy_native_and_reviewed']
    assert not settlement['overall_accepted']
    reports = []

    def retain(folder, lens, number, expected):
        path, value = report(folder, lens, number)
        assert digest(path) == expected['receipt_sha256']
        for key in ['report_sha256', 'raw_stdout_sha256']:
            assert value[key] == expected[key]
        raw = read(value['raw_stdout_path'])
        assert not raw.get('is_error', False)
        assert raw['num_turns'] == value['num_turns'] == 1
        assert value.get('subagents_spawned', 0) == 0
        reports.append(dict(path=str(path), folder=folder, lens=lens, packet=number,
                            receipt_sha256=digest(path), report_sha256=value['report_sha256'],
                            raw_stdout_sha256=value['raw_stdout_sha256'],
                            native_exit=0, actual_context_fit=True))
        return value

    for row in prior['reports']:
        number = int(Path(row['path']).stem.rsplit('-', 1)[1])
        retain(row['folder'], row['lens'], number, row)
    for lens in LENSES:
        expected = next(row for row in settlement['reports'] if row['lens'] == lens)
        assert expected['actual_context_fit'] and expected['fresh_four_files_all_declarations_inspected']
        assert expected['required_fresh_bodies_skipped'] == 0
        value = retain('full105-material-integration-reports', lens, 1, expected)
        covered = set(prior['unchanged_prior_complete_bodies'])
        for row in value['supplied_complete_files']:
            if row['source_kind'] == 'project':
                assert row['sha256'] == old[row['path']]['sha256']
                covered.add(row['path'])
        assert covered == set(old), 'Full344 per-lens body coverage missing'
    assert len(reports) == 39
    return old, reports, dict(parent_source_index_sha256=digest(index_path),
                              parent_graph_sha256=digest(PARENT/'graphs/validated-graphs.json'),
                              parent_reuse_audit_sha256=PRIOR_SHA,
                              parent_settlement_sha256=SETTLEMENT_SHA)


def main(parent_only=False):
    old, reports, pins = parent_review()
    resource = ROOT.parent
    binding = read(resource/'resource-binding.json')
    manifest_path = resource/'capture-manifest.json'
    archive_path = resource/'input-archive.tar.gz'
    assert digest(manifest_path) == binding['files']['capture-manifest.json']
    assert digest(archive_path) == binding['files']['input-archive.tar.gz']
    captured = read(manifest_path)['project_sources']
    assert len(captured) == 346 and sorted(set(captured)-set(old)) == FRESH
    with tarfile.open(archive_path) as archive:
        for rel, row in captured.items():
            data = archive.extractfile(rel).read()
            assert hashlib.sha256(data).hexdigest().upper() == row['sha256']
            assert len(data) == row['bytes']
            if rel in old:
                assert (row['sha256'], row['bytes']) == (old[rel]['sha256'], old[rel]['bytes'])
    pins.update(current_capture_manifest_sha256=digest(manifest_path),
                current_capture_archive_sha256=digest(archive_path),
                all346_capture_body_hashes_verified=True,
                unchanged344_capture_body_hashes_verified=True,
                fresh_capture_body_pins={rel: captured[rel] for rel in FRESH})
    if parent_only:
        value = dict(schema='full107-parent344-body-and39-review-custody-preparation-v2',
                     **pins, project_bodies=344, reports=reports,
                     parent_complete_body_custody_verified=True,
                     Full107_graph_identity_verified=False,
                     Full107_review_acceptance=False, full_goal_complete=False)
        store(HERE/'full107-parent-review-custody-preparation-v2.json', value)
        print(json.dumps(dict(parent_bodies=344, original_reports=39,
                              parent_custody_verified=True, capture_bodies_verified=346,
                              unchanged_parent_capture_bodies_verified=344,
                              successor_identity_verified=False)))
        return
    new_index_path = BASE/'review-sources/source-index.json'
    index = read(new_index_path)
    new = {row['path']: row for row in index['project_bodies']}
    assert len(new) == len(index['project_bodies']) == 346
    assert sorted(set(new)-set(old)) == FRESH
    for rel, row in old.items():
        assert (row['sha256'], row['bytes']) == (new[rel]['sha256'], new[rel]['bytes'])
    for rel, row in new.items():
        path = BASE/'review-sources'/rel
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    graphs = [read(folder/'graphs/validated-graphs.json') for folder in (PARENT, BASE)]
    dags = [read(folder/'type-dag-qualification.json')['type_dag_sha256'] for folder in (PARENT, BASE)]
    assert len(graphs[0]['nodes']) == 8269
    for name, row in graphs[0]['nodes'].items():
        target = graphs[1]['nodes'][name]
        assert dags[0][name] == dags[1][name]
        for field in ['kind', 'module', 'project', 'body_available', 'body_unresolved', 'ownership_unresolved']:
            assert row[field] == target[field]
        for field in ['type_edges', 'proof_edges', 'union_edges']:
            assert set(row[field]) == set(target[field])
    manifests = [read(folder.parent.parent/'capture-manifest.json') for folder in (PARENT, BASE)]
    for field in ['cache_provenance', 'configs']:
        assert manifests[0][field] == manifests[1][field]
    assert graphs[1]['graphs']['exact260-native']['roots'] == manifests[1]['requested_axioms']
    assert len(graphs[1]['graphs']['focused-ninety-two-consumer']['roots']) == 92
    summary = read(BASE/'qualification-summary.json')
    assert summary['structural_trace_qualification'] and not any(summary['unresolved_by_graph'].values())
    value = dict(schema='full107-full344-prior-review-identity-reuse-v1', **pins,
                 new_source_index_sha256=digest(new_index_path),
                 new_graph_sha256=digest(BASE/'graphs/validated-graphs.json'),
                 unchanged_prior_complete_bodies=list(old), fresh_complete_bodies=FRESH,
                 shared_native_type_and_body_dependency_context_unchanged=8269,
                 compiler_package_core_cache_configuration_preserved=True,
                 reports=reports, all344_per_lens_prior_body_coverage_identity_eligible=True,
                 fresh2_body_and_full_integration_review_required=True,
                 prior_scope_findings_and_HIGH_residues_retained=True,
                 current346_fresh_rereading_claimed=False, accepted=False, full_goal_complete=False)
    store(BASE/'prior-review-reuse-audit.json', value)
    store(HERE/'full107-prior-review-reuse-audit-v1.json', value)
    print(json.dumps(dict(prior_bodies=344, fresh_bodies=2, shared_nodes=8269,
                          actual_prior_reports_verified=39, accepted=False)))


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--parent-only'])
    main(sys.argv[1:] == ['--parent-only'])
