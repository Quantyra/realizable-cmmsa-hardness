"""Download a published Linux toolchain archive and verify custody; never execute Lean."""
import hashlib
import json
from pathlib import Path
import shutil
import urllib.request

ROOT = Path('C:/Users/dfred/.quantyra/upstream')


def main():
    release_bytes = (ROOT/'release-check-v4341-v1/response.json').read_bytes()
    release = json.loads(release_bytes)
    if release['tag_name'] != 'v4.34.1' or release.get('draft') or release.get('prerelease'):
        raise ValueError('Unexpected original upstream release')
    assets = [r for r in release['assets'] if r['name'] == 'lean-4.34.1-linux.tar.zst']
    if len(assets) != 1:
        raise ValueError('Required x86 Linux archive absent or ambiguous')
    asset = assets[0]
    digest = asset['digest']
    if digest != 'sha256:47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4' or asset['size'] != 580432872:
        raise ValueError('Published archive identity changed')
    if asset['browser_download_url'] != 'https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst':
        raise ValueError('Unexpected release URL')
    free = shutil.disk_usage(ROOT).free
    reserve = 1610612736
    if free < asset['size'] + reserve:
        raise ValueError('Local custody storage gate failed')
    destination = ROOT/'compiler-archive-v4341-v1'; destination.mkdir()
    partial = destination/'lean-4.34.1-linux.tar.zst.partial'
    request = urllib.request.Request(asset['browser_download_url'], headers={'User-Agent': 'Quantyra-pinned-source-verification'})
    count, next_report, hasher = 0, 67108864, hashlib.sha256()
    with urllib.request.urlopen(request, timeout=45) as response, partial.open('xb') as output:
        if response.status != 200:
            raise ValueError('Release download did not succeed')
        (destination/'response-headers.json').write_text(json.dumps({'status': response.status, 'final_url': response.url, 'headers': dict(response.headers)}, indent=2)+'\n')
        while chunk := response.read(1048576):
            count += len(chunk)
            if count > asset['size']:
                raise ValueError('Archive exceeds published size; preserve partial')
            output.write(chunk); hasher.update(chunk)
            if count >= next_report:
                print('Same original toolchain archive download bytes', count, flush=True)
                next_report += 67108864
    if count != asset['size'] or hasher.hexdigest() != digest.split(':')[1]:
        raise ValueError('Archive custody digest/size failed; preserve partial')
    final = destination/asset['name']; partial.rename(final)
    receipt = {'schema': 'original-upstream-lean4341-archive-custody-v1',
               'published_release_metadata_sha256': hashlib.sha256(release_bytes).hexdigest().upper(),
               'published_asset': asset['name'], 'published_digest': digest,
               'archive_path': str(final), 'archive_sha256': hasher.hexdigest().upper(),
               'bytes': count, 'local_free_before': free, 'local_reserve': reserve,
               'compiler_executed': False, 'compiler_binary_identity_verified': False,
               'upstream_dependency_context_ready': False, 'launch_ready': False, 'accepted': False}
    with (destination/'custody.json').open('x', encoding='utf-8') as output:
        json.dump(receipt, output, indent=2); output.write('\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__': main()
