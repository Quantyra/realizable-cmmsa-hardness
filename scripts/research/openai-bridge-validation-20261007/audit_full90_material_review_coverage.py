"""Snapshot exact completed report scope; missing reports forbid full coverage."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    packet_path = BASE/'material-review-packets-v1/manifest.json'
    packet_bytes = packet_path.read_bytes()
    manifest = json.loads(packet_bytes)
    reports = Path(__file__).parent/'full90-material-review-reports'
    completed, missing, coverage = [], [], {}
    for lens in manifest['required_lenses']:
        coverage[lens] = set()
        for number, packet in enumerate(manifest['packets'], 1):
            key = f'{lens}-{number:02d}'
            receipt_path, report_path = reports/(key+'.json'), reports/(key+'.md')
            if not receipt_path.exists():
                assert not report_path.exists(), 'Unpaired report'
                missing.append(key); continue
            receipt_bytes = receipt_path.read_bytes()
            receipt = json.loads(receipt_bytes)
            assert receipt['lens'] == lens and receipt['packet'] == number
            assert receipt['native_exit'] == 0 and receipt['actual_packet_context_fit']
            assert receipt['packet_sha256'] == packet['sha256']
            assert receipt['supplied_complete_files'] == packet['files']
            assert sha(report_path.read_bytes()) == receipt['report_sha256']
            assert sha(Path(receipt['raw_stdout_path']).read_bytes()) == receipt['raw_stdout_sha256']
            for row in packet['files']:
                source = Path(row['source_root'])/row['path']
                body = source.read_bytes()
                assert len(body) == row['bytes'] and sha(body) == row['sha256']
                coverage[lens].add(row['source_kind']+':'+row['path'])
            completed.append(dict(key=key, receipt_sha256=sha(receipt_bytes),
                                  report_sha256=receipt['report_sha256'], files=len(packet['files'])))
    required = {r['source_kind']+':'+r['path'] for p in manifest['packets'] for r in p['files']}
    result = dict(schema='full90-material-review-scope-snapshot-v1',
                  packet_manifest_sha256=sha(packet_bytes), completed=completed, missing=missing,
                  required_unique_complete_files=len(required),
                  per_lens={lens:dict(supplied_verified_unique_files=len(files),
                                     missing_complete_files=sorted(required-files)) for lens,files in coverage.items()},
                  all_packet_terminals_present=not missing,
                  root_inspection_and_findings_reconciliation_separate=True,
                  integrated_review_complete=False, accepted=False)
    target = BASE/'material-review-coverage-snapshot-v1.json'
    with target.open('x', encoding='utf-8') as output:
        json.dump(result,output,indent=2); output.write('\n')
    print(json.dumps(dict(completed=len(completed),missing=missing,
                         per_lens={k:len(v) for k,v in coverage.items()}, accepted=False)))


if __name__ == '__main__':
    main()
