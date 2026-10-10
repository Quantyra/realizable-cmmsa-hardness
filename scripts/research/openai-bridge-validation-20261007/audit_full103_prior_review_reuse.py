"""Verify prior full327 body/context evidence without granting new acceptance."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full100_prior_review_reuse import report, OLD95, OLD
from full103_consumption_v2_controller import ROOT

HERE = Path(__file__).parent
BASE = ROOT/'qualification-v3'
PARENT = ROOT.parent.parent/'full100-matrix-fourier-bullet-repair-resource02/consumption-v2/qualification'
LENSES = ['proof-adversarial', 'complexity', 'non-claims']


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    indices = [read(root/'review-sources/source-index.json') for root in [PARENT, BASE]]
    old, new = [{row['path']:row for row in index['project_bodies']} for index in indices]
    assert (len(old), len(new)) == (327, 340)
    for rel, row in old.items():
        assert (row['sha256'], row['bytes']) == (new[rel]['sha256'], new[rel]['bytes'])
        for root in [PARENT, BASE]:
            path = root/'review-sources'/rel
            assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    fresh = sorted(set(new)-set(old))
    assert len(fresh) == 13
    graphs = [read(root/'graphs/validated-graphs.json') for root in [PARENT, BASE]]
    dags = [read(root/'type-dag-qualification.json')['type_dag_sha256'] for root in [PARENT, BASE]]
    assert (len(graphs[0]['nodes']), len(graphs[1]['nodes'])) == (8084, 8260)
    for name, row in graphs[0]['nodes'].items():
        target = graphs[1]['nodes'][name]
        assert dags[0][name] == dags[1][name]
        for field in ['kind', 'module', 'project', 'body_available', 'body_unresolved', 'ownership_unresolved']:
            assert row[field] == target[field]
        for field in ['type_edges', 'proof_edges', 'union_edges']:
            assert set(row[field]) == set(target[field])
    manifests = [read(root.parent.parent/'capture-manifest.json') for root in [PARENT, BASE]]
    for field in ['cache_provenance', 'configs']:
        assert manifests[0][field] == manifests[1][field]
    inherited = read(PARENT/'prior-review-reuse-audit.json')
    assert inherited['reuse_identity_eligible'] and inherited['full325_prior_semantic_coverage_identity_eligible']
    assert len(inherited['unchanged_prior_complete_bodies']) == 325
    assert digest(PARENT/'review-sources/source-index.json') == inherited['new_source_index_sha256']
    assert digest(PARENT/'graphs/validated-graphs.json') == inherited['new_graph_sha256']
    earlier = read(OLD95/'prior-review-reuse-audit.json')
    old97 = read(OLD/'prior-review-reuse-audit.json')
    reports = []

    def retain(folder, lens, number=1, expected=None):
        path, value = report(folder, lens, number)
        if expected:
            assert digest(path) == expected['receipt_sha256']
            assert value['report_sha256'] == expected['report_sha256']
        raw = read(value['raw_stdout_path'])
        assert not raw.get('is_error', False) and raw['num_turns'] == value['num_turns'] == 1
        assert value.get('subagents_spawned', 0) == 0
        reports.append(dict(path=str(path), receipt_sha256=digest(path),
            report_sha256=value['report_sha256'], raw_stdout_sha256=value['raw_stdout_sha256'],
            lens=lens, folder=folder, native_exit=0, actual_context_fit=True))
        return value

    assert len(earlier['prior_reports']) == 18
    for row in earlier['prior_reports']:
        retain('full90-material-'+row['kind']+'-reports', row['lens'], row['packet'], row)
    for lens in LENSES:
        for kind, folder in [('original', 'full95-material-integration-reports'),
                             ('addendum', 'full95-material-identity-addendum-reports')]:
            row = next(row for row in old97['six_prior_Full95_reports'] if row['kind'] == kind and row['lens'] == lens)
            retain(folder, lens, expected=row)
        row = next(row for row in inherited['prior_Full97_reports'] if row['lens'] == lens)
        retain('full97-material-integration-reports', lens, expected=row)
        covered = set(inherited['unchanged_prior_complete_bodies'])
        for folder in ['full100-material-integration-reports', 'full100-identity-addendum-reports']:
            value = retain(folder, lens)
            for source in value['supplied_complete_files']:
                if source['source_kind'] == 'project':
                    assert source['sha256'] == old[source['path']]['sha256']
                    covered.add(source['path'])
        assert covered == set(old)
    assert len(reports) == 33
    result = dict(schema='full103-full327-review-identity-reuse-v1',
        old_source_index_sha256=digest(PARENT/'review-sources/source-index.json'),
        new_source_index_sha256=digest(BASE/'review-sources/source-index.json'),
        old_graph_sha256=digest(PARENT/'graphs/validated-graphs.json'),
        new_graph_sha256=digest(BASE/'graphs/validated-graphs.json'),
        unchanged_prior_complete_bodies=list(old), fresh_complete_bodies=fresh,
        shared_native_type_and_body_dependency_context_unchanged=8084,
        compiler_package_core_cache_configuration_preserved=True, reports=reports,
        all327_per_lens_prior_body_coverage_identity_eligible=True,
        fresh13_body_and_full_integration_review_required=True,
        prior_scope_findings_and_HIGH_residues_retained=True,
        current340_fresh_rereading_claimed=False, accepted=False, full_goal_complete=False)
    data = (json.dumps(result, indent=2)+'\n').encode()
    output = BASE/'prior-review-reuse-audit.json'
    if output.exists():
        assert output.read_bytes() == data
    else:
        output.open('xb').write(data)
    Path(__file__).with_name('full103-prior-review-reuse-audit-v1.json').write_bytes(data)
    print(json.dumps(dict(prior_bodies=327, fresh_bodies=13, shared_nodes=8084,
        actual_prior_reports_verified=33, audit_sha256=digest(output), accepted=False)))


if __name__ == '__main__':
    main()
