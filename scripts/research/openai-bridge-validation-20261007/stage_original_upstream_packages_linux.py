"""Run on dedicated GCP only: original offline Git checkouts and pinned patches."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path('/home/dfredriksen_quantyra_org/upstream_adc7f124_original_v1')


def main():
    assert ROOT.is_dir()
    records = []
    log = ROOT/'package-staging-commands.json'
    assert not log.exists()

    def run(args):
        result = subprocess.run(args, capture_output=True)
        records.append(dict(argv=args, native_exit=result.returncode,
                            stdout=result.stdout.decode('utf-8', 'replace'),
                            stderr=result.stderr.decode('utf-8', 'replace')))
        log.write_text(json.dumps(records, indent=2)+'\n')
        result.check_returncode()
        return result.stdout.decode().strip()

    manifest_path = ROOT/'lean/lake-manifest.json'
    assert hashlib.sha256(manifest_path.read_bytes()).hexdigest().upper() == 'CF6105A25D9DCA2F166B241D9191BD12C7E13305890DC9C4D0952351CCCC0794'
    manifest = json.loads(manifest_path.read_bytes())
    packages = ROOT/'lean/.lake/packages'
    packages.mkdir(parents=True, exist_ok=False)
    checks = []
    for p in manifest['packages']:
        assert p['type'] == 'git' and not p['subDir']
        name = p['name'].strip('«»')
        dest = packages/name
        store = ROOT/'git-stores'/(name+'.git')
        assert run(['git', '--git-dir='+str(store), 'rev-parse', 'HEAD']) == p['rev']
        run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(store), str(dest)])
        run(['git', '-C', str(dest), 'remote', 'set-url', 'origin', p['url']])
        run(['git', '-C', str(dest), 'checkout', '--detach', p['rev']])
        assert run(['git', '-C', str(dest), 'rev-parse', 'HEAD']) == p['rev']
        assert run(['git', '-C', str(dest), 'remote', 'get-url', 'origin']) == p['url']
        assert not run(['git', '-C', str(dest), 'status', '--porcelain'])
        checks.append(dict(name=name, revision=p['rev'], origin=p['url'], clean_before_patch=True))
        print('Original checkout verified', name, flush=True)
    plans = []
    for patch in sorted((ROOT/'lean/patches').glob('*-lean4341.patch')):
        name = patch.name.removesuffix('-lean4341.patch')
        dest = packages/name
        assert dest.is_dir()
        run(['git', '-C', str(dest), 'apply', '--check', str(patch)])
        plans.append((patch, dest))
    applied = []
    for patch, dest in plans:
        run(['git', '-C', str(dest), 'apply', str(patch)])
        run(['git', '-C', str(dest), 'apply', '--reverse', '--check', str(patch)])
        applied.append(dict(package=dest.name, patch=patch.name,
                            sha256=hashlib.sha256(patch.read_bytes()).hexdigest().upper(),
                            reverse_check=True))
    receipt = dict(schema='original-upstream-linux-package-staging-v1', checkouts=checks,
                   compatibility_patches=applied, compiler_build_executed=False, accepted=False)
    (ROOT/'package-staging-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(dict(checkouts=len(checks), verified_patches=len(applied), accepted=False)), flush=True)


if __name__ == '__main__':
    main()
