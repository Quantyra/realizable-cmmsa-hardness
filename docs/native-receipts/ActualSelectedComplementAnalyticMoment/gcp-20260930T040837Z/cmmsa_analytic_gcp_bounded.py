import argparse, hashlib, io, json, pathlib, subprocess, tarfile, time

G = r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd'
REPO = pathlib.Path(r'C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness')
FLAGS = ['--project=quantyra-lean-cert-20260915', '--zone=us-central1-a']
VM = 'quantyra-lean-builder-01'

def run(args, timeout=120):
    p = subprocess.run(args, cwd=REPO, capture_output=True, timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
    if p.returncode:
        raise RuntimeError((args, p.returncode, p.stdout.decode(errors='replace'), p.stderr.decode(errors='replace')))
    return p.stdout

def cloud(args, timeout=120):
    return run([G] + args + FLAGS, timeout)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', required=True)
    ap.add_argument('--expected-sha', required=True)
    ap.add_argument('--execute', action='store_true')
    ap.add_argument('--cslib-cache', required=True)
    ap.add_argument('--cslib-sha', required=True)
    a = ap.parse_args()
    source = REPO / a.source
    data = source.read_bytes()
    cache = pathlib.Path(a.cslib_cache)
    assert hashlib.sha256(cache.read_bytes()).hexdigest().lower() == a.cslib_sha.lower()
    assert hashlib.sha256(data).hexdigest().lower() == a.expected_sha.lower()
    tag = 'cmmsa_analytic_' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    base = pathlib.Path(__file__).parent
    archive = base / (tag + '.tar.gz')
    script = base / (tag + '.sh')
    raw = run(['git', 'archive', '--format=tar', 'HEAD', 'lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'], timeout=180)
    with tarfile.open(fileobj=io.BytesIO(raw)) as old, tarfile.open(archive, 'w:gz') as new:
        for member in old:
            if member.name != a.source:
                new.addfile(member, old.extractfile(member) if member.isfile() else None)
        item = tarfile.TarInfo(a.source)
        item.size = len(data)
        new.addfile(item, io.BytesIO(data))
    archive_sha = hashlib.sha256(archive.read_bytes()).hexdigest()
    module = a.source.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
    remote = '''#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=TAG-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p "$HOME/TAG" /tmp/TAG-evidence
trap 'rc=$?; printf "%s\\n" "$rc" >/tmp/TAG-evidence/native-exit; tar -czf /tmp/TAG-evidence.tar.gz -C /tmp/TAG-evidence .; exit "$rc"' EXIT
echo 'ARCHIVESHA  /tmp/TAG.tar.gz' | sha256sum -c -
tar -xzf /tmp/TAG.tar.gz -C "$HOME/TAG"
cd "$HOME/TAG"
mkdir .lake
cp -a "$HOME/realizable-cmmsa-hardness/.lake/packages" .lake/packages
echo 'CACHESHA  /tmp/CACHENAME' | sha256sum -c -
tar -xzf /tmp/CACHENAME -C .lake/packages
test "$(git -C .lake/packages/cslib rev-parse HEAD)" = d9be64196bf145edd019f1ccfeaee0c11166ba6b
mkdir offline-bin
printf '#!/usr/bin/env bash\ncase "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac\nexec /usr/bin/git "$@"\n' >offline-bin/git
chmod +x offline-bin/git
echo 'SOURCESHA  SOURCE' | sha256sum -c -
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/TAG-evidence/toolchain.txt
timeout --signal=TERM --kill-after=20s 900s lake build MODULE >/tmp/TAG-evidence/build.stdout 2>/tmp/TAG-evidence/build.stderr
sha256sum SOURCE .lake/build/lib/lean/MODULEPATH.olean >/tmp/TAG-evidence/pins.sha256
'''
    for key, value in [('CACHESHA', a.cslib_sha), ('CACHENAME', cache.name), ('ARCHIVESHA', archive_sha), ('SOURCESHA', a.expected_sha), ('MODULEPATH', module.replace('.', '/')), ('MODULE', module), ('SOURCE', a.source), ('TAG', tag)]:
        remote = remote.replace(key, value)
    script.write_text(remote, encoding='utf-8', newline='\n')
    print(json.dumps({'prepared': True, 'archive': str(archive), 'script': str(script), 'source_sha': a.expected_sha, 'archive_sha': archive_sha, 'execute': a.execute}, indent=2))
    if not a.execute:
        return
    assert cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).strip() == b'TERMINATED'
    started = False
    try:
        cloud(['compute', 'instances', 'start', VM, '--quiet'], 300)
        started = True
        time.sleep(25)
        cloud(['compute', 'scp', str(archive), str(script), str(cache), VM + ':/tmp/', '--quiet', '--tunnel-through-iap'], 300)
        cloud(['compute', 'ssh', VM, '--quiet', '--tunnel-through-iap', '--command=bash /tmp/' + script.name], 1100)
    finally:
        if started:
            try:
                cloud(['compute', 'scp', VM + ':/tmp/' + tag + '-evidence.tar.gz', str(base / (tag + '-evidence.tar.gz')), '--quiet', '--tunnel-through-iap'], 180)
            finally:
                cloud(['compute', 'instances', 'stop', VM, '--quiet'], 300)
                print('FINAL_VM_STATE', cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).decode().strip())

if __name__ == '__main__':
    main()
