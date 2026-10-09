"""Verify Full95 reuse and six-report custody; no new semantic acceptance."""
import hashlib
import json
from pathlib import Path
from custody_checks import verify_local_custody

BASE = Path('C:/Users/dfred/.quantyra/builder02')
OLD = BASE / 'full95-manuscript-moment-syntax-repair-resource02/consumption-v1/qualification'
NEW = BASE / 'full97-spectral-bridge-utf8-section-repair-resource02/consumption-v1/qualification'
HERE = Path(__file__).parent


def pin(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    old_path = OLD / 'review-sources/source-index.json'
    new_path = NEW / 'review-sources/source-index.json'
    old_index = json.loads(old_path.read_bytes())
    new_index = json.loads(new_path.read_bytes())
    old = {r['path']: r for r in old_index['project_bodies']}
    new = {r['path']: r for r in new_index['project_bodies']}
    if (len(old), len(new)) != (323, 325):
        raise RuntimeError('Full captured body scope required')
    for path, row in old.items():
        target = new.get(path)
        if target is None or (row['sha256'], row['bytes']) != (target['sha256'], target['bytes']):
            raise RuntimeError('Prior source body changed: ' + path)
        for folder in [OLD, NEW]:
            body = folder / 'review-sources' / path
            if pin(body) != row['sha256'] or body.stat().st_size != row['bytes']:
                raise RuntimeError('Complete body bytes changed: ' + path)
    fresh = sorted(set(new) - set(old))
    if fresh != ['lean/PvNP/RealizableHardness/BinaryMatrixSameRangeOrbit.lean',
                 'lean/PvNP/RealizableHardness/SourceSizeContractBridge.lean']:
        raise RuntimeError('Unexpected fresh body scope')
    graphs = [json.loads((q / 'graphs/validated-graphs.json').read_bytes()) for q in [OLD, NEW]]
    dags = [json.loads((q / 'type-dag-qualification.json').read_bytes())['type_dag_sha256'] for q in [OLD, NEW]]
    if len(graphs[0]['nodes']) != 8069 or len(graphs[1]['nodes']) != 8072:
        raise RuntimeError('Unexpected complete native constant scope')
    for name, row in graphs[0]['nodes'].items():
        target = graphs[1]['nodes'].get(name)
        if target is None or dags[0][name] != dags[1][name]:
            raise RuntimeError('Prior native constant/type changed: ' + name)
        for field in ['kind', 'module', 'project', 'body_available', 'body_unresolved', 'ownership_unresolved']:
            if row[field] != target[field]:
                raise RuntimeError('Prior native ownership/body identity changed: ' + name)
        for field in ['type_edges', 'proof_edges', 'union_edges']:
            if set(row[field]) != set(target[field]):
                raise RuntimeError('Prior native dependency edges changed: ' + name)
    manifests = [json.loads((q.parent.parent / 'capture-manifest.json').read_bytes()) for q in [OLD, NEW]]
    if manifests[0]['cache_provenance'] != manifests[1]['cache_provenance'] or manifests[0]['configs'] != manifests[1]['configs']:
        raise RuntimeError('Compiler/package/core/configuration context changed')
    inherited = json.loads((OLD / 'prior-review-reuse-audit.json').read_bytes())
    old90 = BASE / 'full90-material-resource02/consumption-v1/qualification'
    if not inherited['reuse_identity_eligible'] or len(inherited['unchanged_prior_complete_bodies']) != 319:
        raise RuntimeError('Inherited Full90 body coverage absent')
    if pin(old_path) != inherited['new_source_index_sha256'] or pin(old90 / 'review-sources/source-index.json') != inherited['old_source_index_sha256']:
        raise RuntimeError('Inherited source index chain changed')
    if pin(OLD / 'graphs/validated-graphs.json') != inherited['new_graph_sha256'] or pin(old90 / 'graphs/validated-graphs.json') != inherited['old_graph_sha256']:
        raise RuntimeError('Inherited native graph chain changed')
    for row in inherited['prior_reports']:
        folder = HERE / ('full90-material-' + row['kind'] + '-reports')
        receipt = folder / (row['lens'] + '-' + str(row['packet']).zfill(2) + '.json')
        value = json.loads(receipt.read_bytes())
        if pin(receipt) != row['receipt_sha256'] or pin(receipt.with_suffix('.md')) != row['report_sha256']:
            raise RuntimeError('Inherited Full90 report chain changed')
        if value['native_exit'] != 0 or not value['actual_packet_context_fit'] or pin(value['raw_stdout_path']) != value['raw_stdout_sha256']:
            raise RuntimeError('Inherited actual provider evidence changed')
    settlement = json.loads((OLD / 'six-review-custody-v1/typed-custody-settlement.json').read_bytes())
    custody = settlement['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    if not custody['archive_created_locally'] or not settlement['native_exits_all_zero'] or not settlement['actual_provider_context_fits_all_verified']:
        raise RuntimeError('Typed six-review custody/provenance missing')
    reconciliation = json.loads((OLD / 'material-review-root-reconciliation-v1.json').read_bytes())
    if not reconciliation['source_object_category_finding_closed_by_each_lens'] or reconciliation['unconditional_material_or_manuscript_accepted']:
        raise RuntimeError('Prior semantic scope/category settlement inconsistent')
    reports = []
    coverage = {lens: set(inherited['unchanged_prior_complete_bodies']) for lens in ['proof-adversarial', 'complexity', 'non-claims']}
    for kind, folder_name in [('original', 'full95-material-integration-reports'), ('addendum', 'full95-material-identity-addendum-reports')]:
        for lens in coverage:
            path = HERE / folder_name / (lens + '-01.json')
            value = json.loads(path.read_bytes())
            if value['native_exit'] != 0 or not value['actual_packet_context_fit'] or pin(path.with_suffix('.md')) != value['report_sha256'] or pin(value['raw_stdout_path']) != value['raw_stdout_sha256']:
                raise RuntimeError('Prior Full95 provider terminal/report changed')
            for row in value['supplied_complete_files']:
                source = Path(row['source_root']) / row['path']
                if pin(source) != row['sha256'] or source.stat().st_size != row['bytes']:
                    raise RuntimeError('Prior complete supplied body changed')
                if row['source_kind'] == 'project':
                    if row['path'] not in old or row['sha256'] != old[row['path']]['sha256']:
                        raise RuntimeError('Prior report body differs from captured Full95')
                    coverage[lens].add(row['path'])
            reports.append(dict(lens=lens, kind=kind, receipt_sha256=pin(path),
                                report_sha256=value['report_sha256']))
    if any(paths != set(old) for paths in coverage.values()):
        raise RuntimeError('Complete Full323 per-lens prior coverage unproven')
    result = dict(schema='full97-prior-full323-review-reuse-identity-audit-v1',
        old_source_index_sha256=pin(old_path), new_source_index_sha256=pin(new_path),
        old_graph_sha256=pin(OLD / 'graphs/validated-graphs.json'),
        new_graph_sha256=pin(NEW / 'graphs/validated-graphs.json'),
        unchanged_prior_complete_bodies=list(old), changed_prior_bodies=[],
        new_or_changed_complete_bodies=fresh,
        shared_native_constant_types_and_edges_unchanged=8069,
        compiler_package_core_configuration_preserved=True,
        six_prior_Full95_reports=reports, inherited_Full90_reports_verified=len(inherited['prior_reports']),
        prior_conditional_material_verdict=reconciliation['all_three_material_verdicts'],
        prior_remaining_high_scope=reconciliation['remaining_high_scope'],
        prior_remaining_open=reconciliation['remaining_open'],
        typed_review_archive_created_locally=True, actual_compiled_object_binary_custody_not_claimed=True,
        reuse_identity_eligible=True, material_scope_integration_and_critical_reread_required=True,
        new_review_complete=False, accepted=False, full_goal_complete=False)
    with (NEW / 'prior-review-reuse-audit.json').open('x', encoding='utf-8', newline='\n') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    print(json.dumps(dict(prior_bodies=323, fresh_bodies=2, shared_nodes_unchanged=8069,
                         Full95_reports_verified=6, accepted=False)))


if __name__ == '__main__':
    main()
