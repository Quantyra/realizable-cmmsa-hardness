"""Named exact-body coverage audit against preserved actual review receipts."""
import json
from pathlib import Path
from custody_checks import digest
from full100_consumption_v2_controller import ROOT

HERE = Path(__file__).parent
NAMES = {
    'ActualBinaryMatrixHC46OriginalExactInhabitant',
    'ActualSelectedComplementSourceSizeAppendMoment', 'ActualSelectedSpectralParameters',
    'ActualLeafLabelRankImageAlignment', 'ActualComplementCoordinateMassBridge',
    'ActualFixedFunctionalStarMoment', 'ActualRankImageRightBasisInvariance',
    'ActualFiniteMomentLpBounds', 'ActualOrdinaryStarWeightedSelection',
    'ActualStarFixedRhoDimensionGuard', 'SamplerParameters', 'ActualMaximalPairLadder',
    'ActualOccurrenceAllocation', 'ActualSourceStarLaw', 'MatrixLiftNominalDirectComparison',
    'MatrixLiftNominalDomain', 'ActualBinaryGrassmannSamplingBounds',
}
PREFIXES = ('ActualTagged', 'ActualCmmsa', 'MatrixGrassmann')
FOLDERS = ['full89-review-reports', 'full90-material-review-reports', 'full90-material-integration-reports',
           'full95-material-integration-reports', 'full95-material-identity-addendum-reports',
           'full97-material-integration-reports', 'full100-material-integration-reports',
           'full100-identity-addendum-reports']
LENSES = ['proof-adversarial', 'complexity', 'non-claims']


def main(extra_names=(), output_name='spectral-prerequisite-review-coverage-v2.json'):
    index_path = ROOT / 'qualification/review-sources/source-index.json'
    index = json.loads(index_path.read_bytes())
    sources = {r['path']: r for r in index['project_bodies']}
    selected = {p: r for p, r in sources.items()
                if Path(p).stem in NAMES.union(extra_names) or Path(p).stem.startswith(PREFIXES)}
    assert NAMES.union(extra_names) <= {Path(p).stem for p in selected}
    coverage = {p: {lens: [] for lens in LENSES} for p in selected}
    receipts = []
    for folder in FOLDERS:
        for path in sorted((HERE / folder).glob('*.json')):
            receipt = json.loads(path.read_bytes())
            if 'supplied_complete_files' not in receipt:
                continue
            lens = receipt['lens']
            assert lens in LENSES and receipt['native_exit'] == 0
            assert receipt['actual_packet_context_fit']
            assert digest(path.with_suffix('.md')) == receipt['report_sha256']
            assert digest(receipt['raw_stdout_path']) == receipt['raw_stdout_sha256']
            ref = path.relative_to(HERE).as_posix()
            receipts.append(dict(path=ref, sha256=digest(path), report_sha256=receipt['report_sha256']))
            for row in receipt['supplied_complete_files']:
                rel = row['path']
                if rel not in selected:
                    continue
                current = selected[rel]
                if (row['sha256'], row['bytes']) != (current['sha256'], current['bytes']):
                    continue
                source_root = row.get('source_root')
                if source_root is None:
                    assert folder == 'full89-review-reports'
                    source_root = ROOT.parent.parent / 'full89-resource02/consumption-v2/qualification/review-sources'
                body = Path(source_root) / rel
                assert digest(body) == row['sha256'] and body.stat().st_size == row['bytes']
                fresh_body = ROOT / 'qualification/review-sources' / rel
                assert digest(fresh_body) == current['sha256']
                coverage[rel][lens].append(ref)
    rows = [dict(path=p, sha256=selected[p]['sha256'], bytes=selected[p]['bytes'],
                 matching_actual_review_receipts=coverage[p],
                 all_three_lens_body_supply_verified=all(coverage[p][lens] for lens in LENSES))
            for p in sorted(selected)]
    missing = [r['path'] for r in rows if not r['all_three_lens_body_supply_verified']]
    prior = ROOT / 'qualification/prior-review-reuse-audit.json'
    reuse = json.loads(prior.read_bytes())
    assert reuse['reuse_identity_eligible'] and reuse['full325_prior_semantic_coverage_identity_eligible']
    value = dict(schema='spectral-named-prerequisite-review-coverage-v2',
                 source_index_sha256=digest(index_path), reuse_audit_sha256=digest(prior),
                 named_and_prefix_selected_bodies=rows, verified_receipts=receipts,
                 unresolved_three_lens_body_supply=missing,
                 scope='exact body supply to actual successful contextual reviews; inherited conditional verdicts remain',
                 fresh_rereading_claimed=False, native_full101_or_successor_verified=False,
                 manuscript_or_runtime_accepted=False, overall_GO=False)
    data = (json.dumps(value, indent=2) + '\n').encode()
    out = HERE / output_name
    if out.exists():
        assert out.read_bytes() == data
    else:
        out.write_bytes(data)
    print(json.dumps(dict(selected=len(rows), receipts=len(receipts), missing=missing, audit_sha256=digest(out))))


if __name__ == '__main__':
    main()
