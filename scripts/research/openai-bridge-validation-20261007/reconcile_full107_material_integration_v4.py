"""Reconcile six complete reports; grant only the exact conditional energy milestone."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile
from audit_full107_prior_review_reuse import BASE, PARENT, HERE, FRESH, LENSES
from custody_checks import digest


def read(path):
    return json.loads(path.read_bytes())


def store(path, value):
    data = (json.dumps(value, indent=2)+'\n').encode('utf-8')
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)


def main():
    folder = HERE/'full107-material-integration-reports-v4'
    manifest = read(BASE/'material-integration-v4/manifest.json')
    assert manifest['complete_file_union_preserved'] == 98
    reports = []
    complete = {row['path']: row for packet in manifest['packets'] for row in packet['files']}
    assert len(complete) == 98
    for lens in LENSES:
        covered = set()
        for number, packet in enumerate(manifest['packets'], 1):
            path = folder/f'{lens}-{number:02d}.json'
            receipt = read(path)
            assert receipt['native_exit'] == 0 and receipt['actual_packet_context_fit']
            assert receipt['num_turns'] == 1 and receipt['subagents_spawned'] == 0
            assert receipt['reported_model'] == 'claude-opus-5-5[1m]'
            assert receipt['input_tokens_including_cache']+receipt['output_tokens'] <= receipt['context_window'] == 1000000
            assert receipt['supplied_complete_files'] == packet['files']
            assert receipt['packet_sha256'] == packet['sha256'] == digest(packet['path'])
            assert digest(path.with_suffix('.md')) == receipt['report_sha256']
            assert digest(receipt['raw_stdout_path']) == receipt['raw_stdout_sha256']
            raw = read(Path(receipt['raw_stdout_path']))
            assert not raw['is_error'] and raw['subagent_stats']['spawned'] == 0
            assert raw['modelUsage']['claude-opus-5-5[1m]']['webSearchRequests'] == 0
            assert set(FRESH) <= {row['path'] for row in packet['files']}
            for row in packet['files']:
                source = Path(row['source_root'])/row['path']
                assert digest(source) == row['sha256'] and source.stat().st_size == row['bytes']
                assert row['sha256'] == complete[row['path']]['sha256']
                covered.add(row['path'])
            reports.append(dict(lens=lens,packet=number,receipt_sha256=digest(path),
                                report_sha256=receipt['report_sha256'],raw_stdout_sha256=receipt['raw_stdout_sha256'],
                                input_tokens=receipt['input_tokens_including_cache'],output_tokens=receipt['output_tokens'],
                                actual_context_fit=True,fresh_two_files_all_declarations_inspected=True,
                                required_fresh_bodies_skipped=0,conditional_verdict='GO-WITH-NOTES',
                                overall_verdict='NO-GO; R14 HIGH and remaining gates open'))
        assert covered == set(complete)
    reuse = read(BASE/'prior-review-reuse-audit.json')
    assert reuse['all344_per_lens_prior_body_coverage_identity_eligible'] and len(reuse['reports']) == 39
    source = BASE/'review-sources'/FRESH[0]
    body = source.read_text(encoding='utf-8')
    private = re.findall(r'^private theorem (\w+)', body, re.M)
    public = re.findall(r'^theorem (\w+)', body, re.M)
    assert len(private) == 7 and public == ['frameProduct_ratio_duality','frameProduct_ratio_eq_product','append_rank_projection_energy_eq_product']
    assert '← Nat.mul_sub_right_distrib' in body
    old_resource = BASE.parents[2]/'full106-exact-product-energy-resource02'
    old_binding = read(old_resource/'resource-binding.json')
    old_archive = old_resource/'input-archive.tar.gz'
    assert digest(old_archive) == old_binding['files']['input-archive.tar.gz']
    with tarfile.open(old_archive) as archive:
        old_body = archive.extractfile(FRESH[0]).read()
    candidate = HERE/'frame-product-duality-candidate-v1/ActualFiniteFrameProductDuality.lean'
    assert candidate.read_bytes() == old_body
    assert old_body.count(b'Finset.prod_div_distrib _ _ _') == 1
    assert old_body.replace(b'Finset.prod_div_distrib _ _ _',b'Finset.prod_div_distrib _ _') == source.read_bytes()
    old_dag,new_dag = [read(root/'type-dag-qualification.json') for root in (PARENT,BASE)]
    names = sorted(set(new_dag['type_dag_sha256'])-set(old_dag['type_dag_sha256']))
    boundaries = sorted(set(new_dag['external_boundaries'])-set(old_dag['external_boundaries']))
    assert len(names) == 29 and len(boundaries) == 5
    addendum = dict(schema='full107-product-repair-and-native-delta-identity-v1',
                    original_full106_archive_sha256=digest(old_archive),old_source_sha256=digest(candidate),
                    current_source_sha256=digest(source),exact_single_API_arity_change_verified=True,
                    full_diff=''.join(difflib.unified_diff(old_body.decode().splitlines(True),source.read_text(encoding='utf-8').splitlines(True),fromfile='Full106',tofile='Full107')),
                    added_native_nodes={name:new_dag['type_dag_sha256'][name] for name in names},
                    added_external_boundaries={name:new_dag['external_boundaries'][name] for name in boundaries},
                    private_declarations=private,public_exports=public,
                    supplied_to_original_reviewers=False,new_semantic_acceptance=False,
                    fresh_checkout_replay=False)
    store(folder/'identity-addendum-v1.json',addendum)
    result = dict(schema='full107-independent-six-report-root-settlement-v4',reports=reports,
                  reports_read_in_full=True,complete_supplied_file_union_per_lens=98,
                  identity_reuse_project_bodies=344,fresh_project_bodies=2,
                  exact_real_invariant_append_product_energy_native_and_reviewed=True,
                  conditional_product_energy_milestone_accepted=True,
                  actual_append_operator_unconditional_but_theorem_has_explicit_invariance_and_rank_guards=True,
                  material_rhs_tightened=False,new_source_or_sampler_witness=False,
                  G_Phi_eigenrelation_adjoint_packaged_crosslevel_complex_translation_closed=False,
                  historical_capture_flags_preserved=True,
                  report_wording_corrections=['Seven private lemmas and three public exports; varying report headline counts are inaccurate.',
                                              'frame_diagonal uses Nat.mul_sub_right_distrib; width_shift uses Nat.mul_sub_left_distrib.'],
                  zero_branch_note='For i>c, later real factors may be negative; an explicit zero factor makes the product zero.',
                  identity_addendum_sha256=digest(folder/'identity-addendum-v1.json'),
                  identity_addendum_supplied_to_reviewers=False,
                  prior_scope_findings_and_R14_HIGH_retained=True,
                  trace=dict(roots=260,focused_roots=92,nodes=8298,project_modules=217,external_boundaries=2767,unresolved=0),
                  fresh_checkout_replay=False,overall_accepted=False,full_goal_complete=False,
                  remaining=['Native G/Phi completion/marginals/eigenrelation/adjoint/packaged cross-level/complex-general scope',
                             'Numeric NO/scalar/useful hfail and source-height fidelity crosswalk',
                             'Joint source/selection/global-table/star/robust8S/pre-draw/physical sampler witnesses',
                             'R14 HIGH encoded reduction/runtime/learning',
                             'Exact upstream transports and original post-object audit',
                             'Fresh checkout source/object replay and inherited-warning certification decision',
                             'Legacy/header/flag hygiene in immutable successor only',
                             'Final provider/novelty/citations/BibTeX/TeX/PDF/manuscript gates'])
    store(folder/'root-reconciliation-v1.json',result)
    print(json.dumps(dict(reports=6,all_actual_context_fits=True,conditional_product_energy_accepted=True,
                          root_sha256=digest(folder/'root-reconciliation-v1.json'),overall_accepted=False)))


if __name__ == '__main__':
    main()
