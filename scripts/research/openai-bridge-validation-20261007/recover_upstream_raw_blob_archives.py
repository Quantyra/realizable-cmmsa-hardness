"""Repair two preserved Windows archive failures using exact Git object bytes."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

BASE = Path('C:/Users/dfred/.quantyra/upstream')
EXPECTED = 'CF6105A25D9DCA2F166B241D9191BD12C7E13305890DC9C4D0952351CCCC0794'


def main():
    raw = (BASE/'openai-math-adc7f124-20261008/lean/lake-manifest.json').read_bytes()
    if hashlib.sha256(raw).hexdigest().upper() != EXPECTED: raise RuntimeError('Original manifest drift')
    packages = json.loads(raw)['packages']
    for name in ['AINTLIB', 'AbsorptionCutoff']:
        package = next(p for p in packages if p['name'] == name)
        folder = BASE/('original-'+name+'-source-v1')
        repository = folder/'repository.git'
        if (folder/'custody.json').exists(): raise RuntimeError('Recovery already completed; inspect existing receipt')
        prefix = ['git', '--git-dir='+str(repository)]
        actual = subprocess.check_output(prefix+['rev-parse','HEAD']).decode().strip()
        if actual != package['rev']: raise RuntimeError('Fetched repository commit differs')
        tree = subprocess.check_output(prefix+['ls-tree','-r','-z','--full-tree',actual])
        entries = []
        for entry in tree.split(b'\0'):
            if not entry: continue
            header, path = entry.split(b'\t', 1)
            mode, kind, oid = header.decode().split()
            path = path.decode('utf-8')
            if kind != 'blob' or path.startswith('/') or any(p in ('','.','..') for p in path.split('/')):
                raise RuntimeError('Unsupported source tree entry')
            entries.append((path, mode, oid))
        archive_path = folder/'exact-git-blobs-source.tar.gz'
        command = prefix+['cat-file','--batch']
        errors = (folder/'raw-blob-recovery.stderr').open('xb')
        child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors,
                                 creationflags=subprocess.CREATE_NO_WINDOW)
        expected_blobs = {}
        try:
            with archive_path.open('xb') as output, tarfile.open(fileobj=output, mode='w:gz') as archive:
                for path, mode, oid in entries:
                    child.stdin.write((oid+'\n').encode()); child.stdin.flush()
                    header = child.stdout.readline().decode().split()
                    if len(header) != 3 or header[0] != oid or header[1] != 'blob': raise RuntimeError('Git object response mismatch')
                    size = int(header[2]); data = child.stdout.read(size)
                    if len(data) != size or child.stdout.read(1) != b'\n': raise RuntimeError('Incomplete Git blob response')
                    if hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest() != oid: raise RuntimeError('Git blob identity mismatch')
                    member = tarfile.TarInfo(path); member.mode = 0o755 if mode == '100755' else 0o644
                    if mode == '120000':
                        member.type = tarfile.SYMTYPE; member.linkname = data.decode('utf-8'); member.size = 0
                        archive.addfile(member)
                    elif mode in ('100644','100755'):
                        member.size = size; archive.addfile(member, io.BytesIO(data))
                    else: raise RuntimeError('Unsupported Git file mode')
                    expected_blobs[path] = oid
            child.stdin.close()
            code = child.wait()
            if code: raise RuntimeError('Native Git blob recovery failed')
        finally:
            if child.poll() is None: child.terminate(); child.wait()
            errors.close()
        verified = {}
        with tarfile.open(archive_path, 'r:gz') as archive:
            for member in archive.getmembers():
                data = member.linkname.encode() if member.issym() else archive.extractfile(member).read()
                if member.name in verified: raise RuntimeError('Duplicate archive member')
                verified[member.name] = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if verified != expected_blobs: raise RuntimeError('Archive roundtrip differs from original Git objects')
        failed = folder/(name+'-source.tar.gz.partial')
        receipt = {'schema': 'original-upstream-dependency-source-custody-v1', 'upstream_manifest_sha256': EXPECTED,
                   'package': package, 'verified_commit': actual, 'bare_repository': str(repository),
                   'archive_path': str(archive_path), 'archive_sha256': hashlib.sha256(archive_path.read_bytes()).hexdigest().upper(),
                   'archive_bytes': archive_path.stat().st_size, 'tree_listing_sha256': hashlib.sha256(tree).hexdigest().upper(),
                   'git_blobs_verified': len(verified), 'archive_roundtrip_verified': True,
                   'source': 'Direct cat-file Git bytes: no archive conversion or Windows checkout',
                   'preserved_failed_archive': str(failed), 'preserved_failed_archive_sha256': hashlib.sha256(failed.read_bytes()).hexdigest().upper(),
                   'recovery_command': command, 'recovery_native_exit': code, 'windows_source_checkout': False,
                   'compiler_invoked': False, 'patches_applied': False, 'launch_ready': False, 'accepted': False}
        with (folder/'custody.json').open('x', encoding='utf-8') as output:
            json.dump(receipt, output, indent=2); output.write('\n')
        print(json.dumps({'package': name, 'blobs': len(verified), 'archive_sha256': receipt['archive_sha256']}))


if __name__ == '__main__':
    main()
