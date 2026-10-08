"""GCP-only exclusive successor; direct argv execution and native exit custody."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path('/home/dfredriksen_quantyra_org/upstream_adc7f124_original_v1')


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for b in iter(lambda: stream.read(1024*1024), b''):
            h.update(b)
    return h.hexdigest().upper()


def main():
    assert ROOT.is_dir()
    # Never infer terminal from a missing receipt or an expired observation.
    for pid in (3291, 3293, 3543):
        assert not Path('/proc') .joinpath(str(pid)).exists(), 'Original attempt still live'
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            args = (proc/'cmdline').read_bytes().split(b'\0')
        except (OSError, PermissionError):
            continue
        if args and Path(os.fsdecode(args[0])).name in ('lake','lean','curl'):
            raise RuntimeError('Compiler/download process still live; inspect before successor')
    manifest = json.loads((ROOT/'selected-capture-manifest.json').read_bytes())
    for name, pin in manifest['files'].items():
        path = ROOT/name
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
    toolchain = ROOT/'lean-4.34.1-linux'
    assert sha(toolchain/'lib/lean/libleanshared.so') == '6B30CC963D065FC9D2F87F7E9CBE0682B23000AE5425BCCD769C5D477FA74F13'
    version = subprocess.check_output([str(toolchain/'bin/lean'), '--version']).decode()
    assert 'version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
    receipt = json.loads((ROOT/'package-staging-receipt.json').read_bytes())
    assert len(receipt['checkouts']) == 42 and len(receipt['compatibility_patches']) == 23
    for p in receipt['checkouts']:
        repo = ROOT/'lean/.lake/packages'/p['name']
        for args, expected in ((['rev-parse','HEAD'],p['revision']), (['remote','get-url','origin'],p['origin'])):
            assert subprocess.check_output(['git','-C',str(repo),*args]).decode().strip() == expected
    for p in receipt['compatibility_patches']:
        patch = ROOT/'lean/patches'/p['patch']
        assert sha(patch) == p['sha256']
        subprocess.run(['git','-C',str(ROOT/'lean/.lake/packages'/p['package']),
                        'apply','--reverse','--check',str(patch)], check=True)
    destination = ROOT/'original-selected-build-v2'
    destination.mkdir()
    env = dict(os.environ, PATH=str(toolchain/'bin')+':/usr/bin:/bin')
    # Pinned Lake 5.0.0 help confirms this builds locally without network caches.
    command = [str(toolchain/'bin/lake'),'--no-cache','build',*manifest['roots']]
    (destination/'command.json').write_text(json.dumps(dict(argv=command, version=version))+'\n')
    with (destination/'stdout.txt').open('xb') as out, (destination/'stderr.txt').open('xb') as err:
        child = subprocess.Popen(command, cwd=ROOT/'lean', env=env, stdout=out, stderr=err)
        (destination/'live.json').write_text(json.dumps(dict(pid=child.pid, start=time.time()))+'\n')
        while child.poll() is None:
            print('Same original upstream build remains live',child.pid,flush=True)
            time.sleep(30)
    (destination/'native-exit.txt').write_text(str(child.returncode)+'\n')
    print(json.dumps(dict(native_exit=child.returncode, accepted=False)),flush=True)


if __name__ == '__main__':
    main()
