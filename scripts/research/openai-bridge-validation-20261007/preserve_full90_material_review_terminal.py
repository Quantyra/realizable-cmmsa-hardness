"""Preserve an actual terminal report and exact scope; never infer full review acceptance."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification/material-review-packets-v1')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    lens, number = sys.argv[1], int(sys.argv[2])
    manifest = json.loads((ROOT/'manifest.json').read_bytes())
    if lens not in manifest['required_lenses']:
        raise ValueError('Foreign review lens')
    row = manifest['packets'][number-1]
    packet = Path(row['path']).read_bytes()
    folder = ROOT/f'{lens}-{number:02d}'
    prompt = (folder/'prompt.txt').read_bytes()
    if sha(packet) != row['sha256'] or prompt != f'You are the independent {lens} reviewer.\n'.encode() + packet:
        raise ValueError('Review input scope changed')
    raw = (folder/'stdout.json').read_bytes()
    report = json.loads(raw)
    if int((folder/'native-exit.txt').read_text()) != 0 or report['is_error'] or report['terminal_reason'] != 'completed' or report['stop_reason'] != 'end_turn':
        raise ValueError('Review did not finish successfully')
    if report['num_turns'] != 1 or report['subagent_stats']['spawned'] != 0 or not report['result'].strip():
        raise ValueError('Review scope/history unexpected or empty')
    if list(report['modelUsage']) != ['claude-opus-5-5[1m]']:
        raise ValueError('Unexpected reported model')
    usage = report['modelUsage']['claude-opus-5-5[1m]']
    inputs = usage['inputTokens'] + usage['cacheReadInputTokens'] + usage['cacheCreationInputTokens']
    if inputs <= 0 or inputs + usage['outputTokens'] > usage['contextWindow']:
        raise ValueError('Actual context fit absent')
    for tool in ('webSearchRequests',):
        if usage[tool] != 0:
            raise ValueError('Unexpected external tool')
    destination = Path(__file__).parent/'full90-material-review-reports'
    destination.mkdir(exist_ok=True)
    base = destination/f'{lens}-{number:02d}'
    with base.with_suffix('.md').open('x', encoding='utf-8') as output:
        output.write(report['result']+'\n')
    receipt = {'schema': 'full90-independent-material-packet-terminal-v1', 'lens': lens, 'packet': number,
               'packet_sha256': row['sha256'], 'prompt_sha256': sha(prompt),
               'raw_stdout_path': str(folder/'stdout.json'), 'raw_stdout_sha256': sha(raw),
               'raw_stderr_sha256': sha((folder/'stderr.txt').read_bytes()),
               'report_sha256': sha(base.with_suffix('.md').read_bytes()),
               'supplied_complete_files': row['files'], 'supplied_file_count': len(row['files']),
               'native_exit': 0, 'reported_model': 'claude-opus-5-5[1m]', 'canonical_model': usage['canonicalModel'],
               'input_tokens_including_cache': inputs, 'output_tokens': usage['outputTokens'],
               'context_window': usage['contextWindow'], 'actual_packet_context_fit': True,
               'num_turns': 1, 'subagents_spawned': 0,
               'reported_verdict_text': report['result'][:350],
               'root_findings_and_coverage_inspection_required': True,
               'full_lens_coverage_complete': False, 'integration_complete': False, 'accepted': False}
    with base.with_suffix('.json').open('x', encoding='utf-8') as output:
        json.dump(receipt, output, indent=2); output.write('\n')
    print(json.dumps({'lens': lens, 'packet': number, 'files': len(row['files']), 'input_tokens': inputs, 'output_tokens': usage['outputTokens']}))


if __name__ == '__main__': main()
