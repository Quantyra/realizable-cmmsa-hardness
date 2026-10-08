"""Freeze full-body integration windows and exact complete prior-review evidence."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')

GROUPS = [
    ('contracts-and-selected-consumer', [
        'ActualBinaryMatrixHC46A22ParentFactorization', 'ActualBinaryMatrixHC46A22OriginalInduction',
        'ActualBinaryMatrixHC46OriginalExactInhabitant', 'ActualSelectedComplementHC46OriginalApplication',
        'ActualSelectedComplementAnalyticMoment', 'BinaryMatrixFourier', 'ActualBinaryMatrixHC46',
        'ActualBinaryMatrixHC46RealQNorm', 'ActualBinaryMatrixHC46RealQTransport',
        'ActualLeafLabelRankImageAlignment', 'ActualFixedFunctionalMatrixLift',
        'MatrixLiftNominalDirectComparison', 'MatrixLiftExactBudgetZoom']),
    ('analytic-induction-and-incidence', [
        'ActualBinaryMatrixHC46A11WeightedAggregate', 'ActualBinaryMatrixHC46DR6Convolution',
        'ActualBinaryMatrixHC46DR6Incidence', 'ActualBinaryMatrixHC46DR6Mobius',
        'ActualBinaryMatrixHC46DR6Moment', 'ActualBinaryMatrixHC46DR6SignMoments',
        'ActualBinaryMatrixHC46A18OriginalGlobalInduction', 'ActualBinaryMatrixHC46A18InductionBounds',
        'ActualBinaryMatrixHC46A20SquareGlobalness', 'ActualBinaryMatrixHC46A21DyadicMoment']),
    ('carrier-counting-and-transport', [
        'ActualBinaryMatrixHC46A7T1Transfer', 'ActualBinaryMatrixHC46A7WeightedPredecessor',
        'ActualBinaryMatrixHC46A8AmbientAssembly', 'ActualBinaryMatrixHC46A8AveragedAssembly',
        'ActualBinaryMatrixHC46A8AveragedTransport', 'ActualBinaryMatrixHC46A8Endpoint',
        'ActualBinaryMatrixHC46A9AmbientFiber', 'ActualBinaryMatrixHC46A9AmbientReindex',
        'ActualBinaryMatrixHC46CommonA16', 'ActualBinaryMatrixHC46FourierA16',
        'ActualTypedABFullA16Assembly', 'ActualTypedABFullA16Final'])]


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = BASE/'review-sources'
    index_bytes = (source/'source-index.json').read_bytes()
    index = json.loads(index_bytes)
    packet_manifest_bytes = (BASE/'review-packets/manifest.json').read_bytes()
    packets = json.loads(packet_manifest_bytes)
    by_stem = {Path(row['path']).stem: row for row in index['project_bodies']}
    if len(by_stem) != 170:
        raise ValueError('Complete source selection changed')
    native = BASE/'integration-native-evidence-v1'
    evidence_bytes = (native/'native-review-evidence.json').read_bytes()
    evidence = json.loads(evidence_bytes)
    if evidence['requested_root_count'] != 172 or evidence['native_stage_exits'] != [0]*7:
        raise ValueError('Native scope incomplete')
    stdout = (native/'fresh172-native.stdout').read_bytes()
    if sha(stdout) != evidence['fresh172_native_stdout_sha256']:
        raise ValueError('Changed exact native output')
    coverage_bytes = (BASE/'review-packets/native-root-coverage-map.json').read_bytes()
    coverage = json.loads(coverage_bytes)
    compact = {'native_roots': [{'name': r['name'], 'kind': r['kind'], 'module': r['module'],
                                'packet': r['complete_source']['packet'],
                                'source_sha256': r['complete_source']['sha256']} for r in coverage['native_roots']],
               'focused_consumers': {n: {'reachable_constants': r['reachable_constants'],
                                        'required_packets': r['required_packets'],
                                        'external_boundaries': r['external_boundary_count']}
                                     for n, r in coverage['focused_consumers'].items()},
               'complete_root_coverage_map_sha256': sha(coverage_bytes),
               'all170_source_pins': index['project_bodies'],
               'external_library_source_module_count': index['external_module_count'],
               'external_boundary_count': len(index['external_boundaries']),
               'external_source_custody_complete': index['external_source_custody_complete'],
               'external_libraries_newly_reviewed': False,
               'full_source_index_sha256': sha(index_bytes)}
    instructions = '''Independent Full89 cross-partition integration, not full-manuscript closeout.
The complete native milestone is original natural-dyadic-p A22 with real conjugate q, unrestricted-eta HC46 and the same selected leaf consumer. Do not replace it with an easier conditional theorem. All170 full selected bodies have actual prior three-lens reports, included below in full; reuse only their exact unchanged source/dependency/native identities. Current full-body windows recheck cross-partition contracts and critical transitions. No tool use, writes, code, Lean/Lake or subagents.
Every packet verdict is limited; HIGH findings are not closed by GO-WITH-NOTES. Independently resolve (or retain) every HIGH/Medium question that this window's actual source/evidence can address. Do not merely endorse Root's dispositions. Root notes are hypotheses for review, not proof.
Check the universal original_HC46_exact : HC46ExactContract, original selected wrappers and whether that universal theorem can instantiate hHC in the SAME material-moment consumer; distinguish logical availability from a dedicated hHC-free material export. Spectral47 and useful numerical NO bounds remain open: do not infer complete material-moment/reduction/runtime/learning acceptance. Inspect exact nominal-budget padding/whole fibres/nonnegative eta/zero density and actual-exact-budget flag averaging, strict rank guards, same predrawn T/f and factor2. PseudorandomExact is a one-sided density upper bound, not a two-sided theorem.
Check A11's genuine strict-lower-degree hS discharge, actual A9 fibre/partition, A8 overlap/cubic costs, DR6 signed incidence/normalization, A18/A21/A22 dependency direction and constants, typed A14/A15/A16 definitions and transports. Legacy degenerate A7/A9 helpers must not be credited as the final route. Trace-based absence is bounded to the exact172 roots/focused-four, not all repository uses.
Actual fresh172 stdout is supplied verbatim. Native all7 zero, all319 source pins, 566 unchanged warm objects and compiler/core/package identities are established in qualified receipts. Zero OWNED warnings and zero inherited regressions are distinct from zero TOTAL warnings; inherited baseline debt remains open. Historical source comments do not certify or invalidate native evidence, and native GREEN does not replace review acceptance. Pinned Init/Mathlib/Batteries source/kernel trust is explicit; do not pretend every library body was newly reviewed.
Manuscript/render/novelty and broader Spectral47/source/star/robust8S/numericNO/encoded reduction/runtime/learning/upstream/fresh-checkout/final-provider gates remain open. No full-manuscript verdict is requested or authorized by this window. Identify exact missing source/statement/type/manuscript evidence rather than guess. Emit GO/GO-WITH-NOTES/NO-GO/INCOMPLETE FOR THIS WINDOW, all complete supplied bodies inspected/skipped, explicit per-finding dispositions with declarations/evidence, unresolved cross-window questions and exact safe claim boundary. Any skipped required body or unresolved HIGH issue keeps integration incomplete.
'''
    common = instructions + '\nABSOLUTE SOURCE DESTINATION: '+str(source)+'\n'
    common += '\nEXACT NATIVE STDOUT\n'+stdout.decode()
    common += '\nNATIVE EVIDENCE\n'+json.dumps(evidence, separators=(',', ':'))
    qualified_path = BASE.parents[1]/'checks/20261008T094603813465Z/qualified-native/cmmsa_a8_output_20261008T094623Z_e93b94e1/successor-native-report.json'
    qualified_bytes = qualified_path.read_bytes()
    if sha(qualified_bytes) != '2705033D11D82200894111F915C8FFF04CDF966FB6678B4A67D499A09E43B4B7':
        raise ValueError('Qualified native audit changed')
    common += '\nQUALIFIED NATIVE AUDIT\n'+qualified_bytes.decode()
    legacy_path = Path(__file__).with_name('full89-legacy-a7-consumption-disposition.json')
    common += '\nBOUNDED ACTUAL LEGACY A7 CONSUMPTION DISPOSITION\n'+legacy_path.read_text(encoding='utf-8')
    common += '\nBOUNDED ACTUAL A9 CONSUMPTION DISPOSITION\n'+(PLANNING/'docs/research/pvnp/full89-actual-a9-consumption-disposition-2026-10-08.json').read_text(encoding='utf-8-sig')
    graph = json.loads((BASE/'graphs/validated-graphs.json').read_bytes())
    unused_aliases = ['PvNP.RealizableHardness.MatrixLiftFullRowRankBridge.'+name for name in
                      ['binary_affine_target_score_sum_le_twice', 'binary_affine_target_mean_le_twice', 'binary_affine_target_zoom_density_le_two_e']]
    if any(name in graph['nodes'] or name in evidence['actual_profiles'] for name in unused_aliases):
        raise ValueError('Inferred-type alias actually consumed; supply its full native type')
    common += '\nINFERRED-TYPE BRIDGE ALIASES: absent from the complete172 root trace and not requested native roots; do not credit their inferred types as final-route evidence. '+json.dumps(unused_aliases)+'\n'
    common += '\nEXACT ROOT/SOURCE COVERAGE\n'+json.dumps(compact, separators=(',', ':'))
    dispositions = (PLANNING/'docs/research/pvnp/full89-review-integration-dispositions-2026-10-08.md').read_bytes()
    common += '\nROOT DISPOSITIONS TO CHALLENGE\n'+dispositions.decode('utf-8-sig')
    reviews = []
    for lens in packets['required_lenses']:
        for number, packet in enumerate(packets['packets'], 1):
            folder = BASE/f'review-packets/{lens}-{number:02d}'
            raw = (folder/'stdout.json').read_bytes()
            report = json.loads(raw)
            if int((folder/'native-exit.txt').read_text()) != 0 or report['is_error'] or report['stop_reason'] != 'end_turn' or report['num_turns'] != 1:
                raise ValueError('Prior review not complete')
            original = Path(packet['path']).read_bytes()
            if sha(original) != packet['sha256'] or (folder/'prompt.txt').read_bytes() != f'You are the independent {lens} reviewer.\n'.encode()+original:
                raise ValueError('Prior complete body scope changed')
            common += f'\nFULL PRIOR REPORT {lens} packet{number}; raw SHA256 {sha(raw)}; complete supplied files {len(packet["files"])}\n'+report['result']+'\n'
            reviews.append({'lens': lens, 'packet': number, 'raw_stdout_sha256': sha(raw), 'packet_sha256': packet['sha256']})
    destination = BASE/'integration-v1-evidence-complete'; destination.mkdir()
    windows = []
    for number, (label, names) in enumerate(GROUPS, 1):
        text = common + f'\nCURRENT INTEGRATION WINDOW {number}/3: {label}\n'
        rows = []
        for name in names:
            row = by_stem[name]
            data = (source/row['path']).read_bytes()
            if sha(data) != row['sha256'] or len(data) != row['bytes']:
                raise ValueError('Critical source changed: '+name)
            text += f'\n=== COMPLETE FILE {row["path"]} SHA256 {row["sha256"]} ===\n'+data.decode()+'\n=== END COMPLETE FILE ===\n'
            rows.append(row)
        data = text.encode()
        if len(data) >= 850000:
            raise ValueError(f'Integration window{number} byte bound exceeded: {len(data)}')
        path = destination/f'window-{number:02d}.txt'; path.write_bytes(data)
        windows.append({'path': str(path), 'label': label, 'sha256': sha(data), 'bytes': len(data), 'files': rows})
    manifest = {'schema': 'full89-cross-partition-integration-v1', 'packets': windows,
                'required_lenses': packets['required_lenses'], 'complete_prior_reports': reviews,
                'prior_review_count': 27, 'common_evidence_bytes': len(common.encode()),
                'source_index_sha256': sha(index_bytes), 'native_evidence_sha256': sha(evidence_bytes),
                'actual_provider_context_fit_verified': False, 'all_windows_required': True,
                'final_synthesis_required': True, 'accepted': False}
    (destination/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'windows': [(p['label'], p['bytes'], len(p['files'])) for p in windows], 'prior_reports': 27}))


if __name__ == '__main__': main()
