"""Freeze complete integration evidence only after all nine windows terminate."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')
WINDOWS = BASE/'integration-v1-evidence-complete'
DESTINATION = BASE/'integration-synthesis-v1'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    manifest_bytes = (WINDOWS/'manifest.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    verified = []
    bodies = {}
    reports = []
    common = None
    for number, row in enumerate(manifest['packets'], 1):
        packet = Path(row['path']).read_bytes()
        if sha(packet) != row['sha256']:
            raise ValueError('Integration source packet changed')
        current_common = packet.split(b'\nCURRENT INTEGRATION WINDOW ', 1)[0]
        if common is None:
            common = current_common
        elif current_common != common:
            raise ValueError('Different common evidence across windows')
        for source in row['files']:
            path = BASE/'review-sources'/source['path']
            data = path.read_bytes()
            if sha(data) != source['sha256'] or len(data) != source['bytes']:
                raise ValueError('Complete source body changed')
            previous = bodies.get(source['path'])
            if previous and previous[0] != source:
                raise ValueError('Inconsistent source pin')
            bodies[source['path']] = (source, data)
        for lens in manifest['required_lenses']:
            folder = WINDOWS/f'{lens}-{number:02d}'
            raw = (folder/'stdout.json').read_bytes()
            report = json.loads(raw)
            receipt_path = Path(__file__).with_name('full89-integration-reports')/f'{lens}-{number:02d}.json'
            receipt = json.loads(receipt_path.read_bytes())
            if (folder/'prompt.txt').read_bytes() != f'You are the independent {lens} reviewer.\n'.encode()+packet:
                raise ValueError('Window prompt changed')
            if int((folder/'native-exit.txt').read_text()) != 0 or report['is_error']:
                raise ValueError('Unsuccessful integration window')
            if report['terminal_reason'] != 'completed' or report['stop_reason'] != 'end_turn' or report['num_turns'] != 1 or report['subagent_stats']['spawned'] != 0:
                raise ValueError('Incomplete or unexpected review history')
            if sha(raw) != receipt['raw_stdout_sha256'] or receipt['packet_sha256'] != row['sha256'] or not receipt['actual_packet_context_fit']:
                raise ValueError('Terminal receipt mismatch')
            if list(report['modelUsage']) != ['claude-opus-5-5[1m]'] or not report['result'].strip():
                raise ValueError('Missing actual model or report')
            reports.append(f'\nFULL INTEGRATION REPORT {lens} window{number}; raw SHA256 {sha(raw)}\n'+report['result']+'\n')
            verified.append({'lens': lens, 'window': number, 'raw_stdout_sha256': sha(raw), 'receipt_sha256': sha(receipt_path.read_bytes())})
    if len(verified) != 9 or len(bodies) != 35:
        raise ValueError('Incomplete cross-window scope')
    instructions = '''FINAL INDEPENDENT CROSS-PARTITION INTEGRATION SYNTHESIS.
This supersedes the per-window request below solely for this invocation. Integrate all three windows and all three lenses, rather than issue another window-only verdict. All 35 cross-partition bodies are supplied COMPLETE, together with all nine window reports and all 27 prior complete-body packet reports. Read all supplied bodies; explicitly report inspected/skipped counts. Reuse unchanged prior 170-file body reviews only under their exact source/native identities. Do not use tools, write files, run Lean/Lake, or spawn subagents.
Independently reconcile every HIGH and Medium finding and distinguish resolved leaf/native contract questions from still-open full material-moment, Spectral47, numeric-NO and manuscript obligations. Window2 retained some HIGH questions because the window1 bodies were absent there: they are present together here. Recheck these bodies and give a declaration/evidence-based disposition, not a vote of prior verdicts. Native source/object closure is real but does not imply a fresh material declaration profile or an HC-free material export. No dedicated such export is supplied. Do not conflate absence from the 172-root/four-consumer trace with absence of source/object compile evidence or absence from all repository uses.
Correct any prior report saying that all constants in the 319 compiled modules have standard axiom profiles merely because the modules compile: the fresh standard-axiom evidence covers the requested roots and their transitive constant closures, not every declaration in every compiled file. Distinguish imported-but-unconsumed module compilation from reachable declaration axiom evidence.
Check the SAME natural-dyadic-p A22, real conjugate q, unrestricted-eta HC46 and same predrawn-T/f selected leaf consumer, original induction and carrier/counting/normalization transitions. Do not narrow those native statements to easier conditional replacements. State precisely which integration conclusions are proved, incomplete, contradicted or unsupported. Any skipped required body or unresolved HIGH issue prevents an overall integration GO. Separately label the selected-leaf/native integration verdict and the full material/manuscript readiness verdict. Broader source/star/robust8S, reduction/runtime/learning, upstream builds/bridges, warning disposition, fresh-checkout, manuscript fidelity/render/novelty/citations and final full-scope provider gates remain open; this review cannot certify the full manuscript.
Produce a reconciled per-finding table with exact declarations, severity, disposition, evidence and remaining actions; required missing bodies or profiles; the bounded safe claim; and an explicit remaining to-do list. No invented proof, compile result, citation or acceptance.
'''
    text = instructions.encode()+b'\nPRESERVED COMMON EVIDENCE AND PRIOR REPORTS\n'+common
    coverage_bytes = Path(__file__).with_name('full89-integration-consumption-coverage.json').read_bytes()
    coverage = json.loads(coverage_bytes)
    if coverage['graph_sha256'] != sha((BASE/'graphs/validated-graphs.json').read_bytes()) or coverage['source_index_sha256'] != sha((BASE/'review-sources/source-index.json').read_bytes()) or coverage['project_modules_outside_selection']:
        raise ValueError('Bounded consumption coverage evidence mismatch')
    text += b'\nBOUNDED TRACE COVERAGE AND REACHED LEGACY-MODULE CONSTANTS (address window3 N1 and window2 N4)\n'+coverage_bytes
    text += ''.join(reports).encode()
    for path, (row, data) in bodies.items():
        text += f'\n=== COMPLETE FILE {path} SHA256 {row["sha256"]} ===\n'.encode()+data+b'\n=== END COMPLETE FILE ===\n'
    if len(text) >= 1800000:
        raise ValueError('Synthesis requires another complete-body context strategy')
    DESTINATION.mkdir()
    path = DESTINATION/'synthesis.txt'
    path.write_bytes(text)
    output = {'schema': 'full89-integration-synthesis-v1', 'required_lenses': manifest['required_lenses'],
              'packets': [{'path': str(path), 'sha256': sha(text), 'bytes': len(text), 'files': [r for r, d in bodies.values()]}],
              'verified_prior_integration_terminals': verified, 'window_manifest_sha256': sha(manifest_bytes),
              'actual_provider_context_fit_verified': False, 'accepted': False,
              'full_material_and_manuscript_gates_open': True}
    (DESTINATION/'manifest.json').write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'bytes': len(text), 'complete_bodies': len(bodies), 'prior_integration_reports': len(verified), 'sha256': sha(text)}))


if __name__ == '__main__':
    main()
