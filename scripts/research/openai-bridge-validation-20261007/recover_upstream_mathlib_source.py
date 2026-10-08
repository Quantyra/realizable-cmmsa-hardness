"""Recover the original upstream Mathlib commit without checkout or compilation."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

UPSTREAM = Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
DESTINATION = UPSTREAM.parent/'original-mathlib-source-v1'
MANIFEST_SHA = 'CF6105A25D9DCA2F166B241D9191BD12C7E13305890DC9C4D0952351CCCC0794'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    manifest_path = UPSTREAM/'lean/lake-manifest.json'
    if sha(manifest_path) != MANIFEST_SHA:
        raise RuntimeError('Original upstream dependency manifest changed')
    pinned_blob = subprocess.check_output(['git', '-C', str(UPSTREAM), 'show',
                                          'adc7f1241b42e322a6451854ab7e4b4c146bf78a:lean/lake-manifest.json'])
    if pinned_blob != manifest_path.read_bytes():
        raise RuntimeError('Working manifest differs from original pinned Git blob')
    manifest = json.loads(manifest_path.read_bytes())
    package = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if package['type'] != 'git' or package['url'] != 'https://github.com/leanprover-community/mathlib4.git' or package['rev'] != 'd13f23b723b8a846827a245b89c10fc7d3f11612':
        raise RuntimeError('Original Mathlib source pin differs')
    free_before = shutil.disk_usage(UPSTREAM).free
    if free_before < 1536*1024**2 + 512*1024**2:
        raise RuntimeError('Insufficient custody reserve for source recovery')
    DESTINATION.mkdir()
    repository = DESTINATION/'repository.git'
    records = []
    env = dict(os.environ, GIT_TERMINAL_PROMPT='0')

    def git(args, output_file=None):
        command = ['git', '-c', 'core.autocrlf=false', *args]
        output = output_file.open('xb') if output_file else subprocess.PIPE
        child = subprocess.Popen(command, stdout=output, stderr=subprocess.PIPE, env=env,
                                 creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try: out, err = child.communicate(timeout=30); break
            except subprocess.TimeoutExpired: print('Same pinned upstream Git recovery remains live', child.pid, flush=True)
        if output_file: output.close()
        number = len(records)
        if not output_file: (DESTINATION/f'{number}.stdout').write_bytes(out)
        (DESTINATION/f'{number}.stderr').write_bytes(err)
        records.append({'argv': command, 'native_exit': child.returncode,
                        'utc': datetime.now(timezone.utc).isoformat(), 'binary_output_path': str(output_file) if output_file else None})
        (DESTINATION/'commands.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        if child.returncode: raise RuntimeError('Pinned Git recovery failed; retain existing files/handle')
        return out

    git(['init','--bare',str(repository)])
    git(['--git-dir='+str(repository),'fetch','--depth=1',package['url'],package['rev']])
    actual = git(['--git-dir='+str(repository),'rev-parse','FETCH_HEAD']).decode().strip()
    if actual != package['rev']: raise RuntimeError('Fetched commit differs from original manifest')
    git(['--git-dir='+str(repository),'update-ref','refs/heads/frozen',actual])
    git(['--git-dir='+str(repository),'symbolic-ref','HEAD','refs/heads/frozen'])
    tree_bytes = git(['--git-dir='+str(repository),'ls-tree','-r','-z','--full-tree',actual])
    expected = {}
    for entry in tree_bytes.split(b'\0'):
        if not entry: continue
        header, path = entry.split(b'\t', 1)
        mode, kind, oid = header.decode().split()
        if kind != 'blob': raise RuntimeError('Nested repository needs separate source recovery')
        expected[path.decode('utf-8')] = (mode, oid)
    partial = DESTINATION/'mathlib-source.tar.gz.partial'
    git(['--git-dir='+str(repository),'archive','--format=tar.gz',actual], partial)
    verified = {}
    with tarfile.open(partial, 'r:gz') as archive:
        for member in archive.getmembers():
            if member.isdir(): continue
            if member.name.startswith('/') or '..' in member.name.split('/') or member.name not in expected:
                raise RuntimeError('Unexpected source archive path')
            if member.name in verified: raise RuntimeError('Duplicate source archive path')
            data = member.linkname.encode() if member.issym() else archive.extractfile(member).read()
            oid = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if oid != expected[member.name][1]: raise RuntimeError('Archive differs from original Git blob: '+member.name)
            verified[member.name] = oid
    if set(verified) != set(expected): raise RuntimeError('Incomplete original dependency source archive')
    archive_path = partial.with_suffix('')
    partial.rename(archive_path)
    receipt = {'schema': 'original-upstream-mathlib-source-custody-v1', 'upstream_manifest_sha256': MANIFEST_SHA,
               'package': package, 'verified_commit': actual, 'bare_repository': str(repository),
               'archive_path': str(archive_path), 'archive_sha256': sha(archive_path), 'archive_bytes': archive_path.stat().st_size,
               'tree_listing_sha256': hashlib.sha256(tree_bytes).hexdigest().upper(), 'git_blobs_verified': len(verified),
               'disk_free_before': free_before, 'disk_free_after': shutil.disk_usage(UPSTREAM).free,
               'windows_source_checkout': False, 'compiler_invoked': False, 'patches_applied': False,
               'all42_packages_recovered': False, 'launch_ready': False, 'accepted': False}
    (DESTINATION/'custody.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'archive_sha256': receipt['archive_sha256'], 'bytes': receipt['archive_bytes'],
                      'git_blobs_verified': len(verified), 'compiler_invoked': False}), flush=True)


if __name__ == '__main__':
    main()
