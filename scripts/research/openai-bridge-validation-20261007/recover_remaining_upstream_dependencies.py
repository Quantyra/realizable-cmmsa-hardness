"""Recover all original manifest sources sequentially; preserve failures and partials."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

BASE = Path('C:/Users/dfred/.quantyra/upstream')
MANIFEST = BASE/'openai-math-adc7f124-20261008/lean/lake-manifest.json'
EXPECTED = 'CF6105A25D9DCA2F166B241D9191BD12C7E13305890DC9C4D0952351CCCC0794'


def main():
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest().upper() != EXPECTED:
        raise RuntimeError('Original dependency manifest changed')
    packages = json.loads(raw)['packages']
    folder = BASE/'original-dependencies-recovery-v1'
    folder.mkdir()
    records = []
    for package in packages:
        slug = package['name'].removeprefix('«').removesuffix('»')
        destination = BASE/('original-'+slug+'-source-v1')
        receipt = destination/'custody.json'
        if not receipt.exists():
            if destination.exists():
                records.append({'package': package['name'], 'status': 'preserved partial: inspection required'})
            else:
                command = [sys.executable, '-B', '-X', 'utf8', str(Path(__file__).with_name('recover_upstream_dependency_source.py')), package['name']]
                process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                           creationflags=subprocess.CREATE_NO_WINDOW)
                while True:
                    try: out, err = process.communicate(timeout=30); break
                    except subprocess.TimeoutExpired:
                        print('Same original dependency recovery remains live', package['name'], process.pid, flush=True)
                number = len(records)
                (folder/f'{number}.stdout').write_bytes(out)
                (folder/f'{number}.stderr').write_bytes(err)
                records.append({'package': package['name'], 'argv': command, 'native_exit': process.returncode,
                                'utc': datetime.now(timezone.utc).isoformat(), 'status': 'recovered' if process.returncode == 0 else 'failed; partial preserved'})
        if receipt.exists():
            data = json.loads(receipt.read_bytes())
            archive = Path(data['archive_path'])
            if data['package'] != package or data['upstream_manifest_sha256'] != EXPECTED or hashlib.sha256(archive.read_bytes()).hexdigest().upper() != data['archive_sha256']:
                raise RuntimeError('Existing dependency custody identity differs: '+package['name'])
            if not records or records[-1]['package'] != package['name']:
                records.append({'package': package['name'], 'status': 'existing verified custody'})
            records[-1].update(receipt_path=str(receipt), receipt_sha256=hashlib.sha256(receipt.read_bytes()).hexdigest().upper(),
                               verified_commit=data['verified_commit'], archive_sha256=data['archive_sha256'],
                               archive_bytes=data['archive_bytes'], git_blobs_verified=data['git_blobs_verified'])
        (folder/'progress.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        print(json.dumps({'package': package['name'], 'status': records[-1]['status']}, ensure_ascii=False), flush=True)
    recovered = [r for r in records if 'receipt_path' in r]
    summary = {'schema': 'original-upstream-all-dependency-source-recovery-v1', 'manifest_sha256': EXPECTED,
               'manifest_package_count': len(packages), 'recovered_count': len(recovered), 'records': records,
               'all42_dependency_sources_recovered': len(recovered) == 42,
               'patches_applied': False, 'compiler_invoked': False, 'launch_ready': False, 'accepted': False}
    (folder/'summary.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'recovered': len(recovered), 'required': len(packages), 'compiler_invoked': False}), flush=True)


if __name__ == '__main__':
    main()
