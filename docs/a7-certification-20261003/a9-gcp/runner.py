import argparse, hashlib, io, json, pathlib, re, subprocess, tarfile, tempfile, time, traceback

G = r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd'
REPO = pathlib.Path(r'C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness')
FLAGS = ['--project=quantyra-lean-cert-20260915', '--zone=us-central1-a']
VM = 'quantyra-lean-builder-01'
RUN_LOG_DIRECTORY = None
COMMAND_RECORDS = []

def run(args, timeout=120):
    p = subprocess.run(args, cwd=REPO, capture_output=True, timeout=timeout, creationflags=subprocess.CREATE_NO_WINDOW)
    if RUN_LOG_DIRECTORY is not None and args[0] == G:
        RUN_LOG_DIRECTORY.mkdir(parents=True, exist_ok=True)
        index = len(COMMAND_RECORDS)
        (RUN_LOG_DIRECTORY / (str(index) + '.stdout')).write_bytes(p.stdout)
        (RUN_LOG_DIRECTORY / (str(index) + '.stderr')).write_bytes(p.stderr)
        COMMAND_RECORDS.append({'args': args, 'native_exit_code': p.returncode,
            'stdout_sha256': hashlib.sha256(p.stdout).hexdigest(),
            'stderr_sha256': hashlib.sha256(p.stderr).hexdigest()})
        (RUN_LOG_DIRECTORY / 'commands.json').write_text(json.dumps(COMMAND_RECORDS, indent=2), encoding='utf-8')
    if p.returncode:
        if RUN_LOG_DIRECTORY is not None:
            RUN_LOG_DIRECTORY.mkdir(parents=True, exist_ok=True)
            (RUN_LOG_DIRECTORY / 'failed-command.stdout').write_bytes(p.stdout)
            (RUN_LOG_DIRECTORY / 'failed-command.stderr').write_bytes(p.stderr)
            (RUN_LOG_DIRECTORY / 'failed-command.json').write_text(json.dumps({
                'args': args, 'native_exit_code': p.returncode,
                'stdout_sha256': hashlib.sha256(p.stdout).hexdigest(),
                'stderr_sha256': hashlib.sha256(p.stderr).hexdigest()
            }, indent=2), encoding='utf-8')
        raise RuntimeError((args, p.returncode, p.stdout.decode(errors='replace'), p.stderr.decode(errors='replace')))
    return p.stdout

def cloud(args, timeout=120):
    return run([G] + args + FLAGS, timeout)

def main():
    global RUN_LOG_DIRECTORY
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', required=True)
    ap.add_argument('--expected-sha', required=True)
    ap.add_argument('--execute', action='store_true')
    ap.add_argument('--independent-batch', action='store_true')
    ap.add_argument('--direct-development', action='store_true')
    ap.add_argument('--required-object-pin', action='append', default=[])
    ap.add_argument('--cslib-cache')
    ap.add_argument('--cslib-sha')
    ap.add_argument('--reuse-tag')
    ap.add_argument('--dependency-source', action='append', default=[])
    ap.add_argument('--dependency-sha', action='append', default=[])
    ap.add_argument('--dependency-snapshot', action='append', default=[],
                    help='Uncompiled overlay as repository-source=durable-snapshot-path')
    ap.add_argument('--prebuild-source', action='append', default=[])
    ap.add_argument('--prebuild-snapshot', action='append', default=[],
                    help='Explicit compiled prebuild overlay as repository-source=durable-snapshot-path')
    a = ap.parse_args()
    if a.reuse_tag:
        assert re.fullmatch(r'cmmsa_analytic_\d{8}T\d{6}Z', a.reuse_tag)
    source = REPO / a.source
    data = source.read_bytes()
    cache = pathlib.Path(a.cslib_cache) if a.cslib_cache else None
    if not a.reuse_tag:
        assert cache is not None and a.cslib_sha is not None
        assert hashlib.sha256(cache.read_bytes()).hexdigest().lower() == a.cslib_sha.lower()
    assert hashlib.sha256(data).hexdigest().lower() == a.expected_sha.lower()
    assert len(a.dependency_source) == len(a.dependency_sha)
    overlays = {a.source: data}
    overlay_pins = {a.source: a.expected_sha}
    snapshots = dict(item.split('=', 1) for item in a.dependency_snapshot)
    assert set(snapshots) <= set(a.dependency_source)
    assert not set(snapshots).intersection(a.prebuild_source)
    compiled_snapshots = dict(item.split('=', 1) for item in a.prebuild_snapshot)
    assert set(compiled_snapshots) <= set(a.prebuild_source)
    assert set(compiled_snapshots) <= set(a.dependency_source)
    assert not set(compiled_snapshots).intersection(snapshots)
    snapshots.update(compiled_snapshots)
    for dep, pin in zip(a.dependency_source, a.dependency_sha):
        assert dep.startswith('lean/') and dep.endswith('.lean') and '..' not in dep
        payload_path = (REPO / snapshots.get(dep, dep)).resolve()
        assert payload_path.is_relative_to(REPO.resolve())
        payload = payload_path.read_bytes()
        assert hashlib.sha256(payload).hexdigest().lower() == pin.lower()
        assert dep not in overlays
        overlays[dep] = payload
        overlay_pins[dep] = pin
    for pre in a.prebuild_source:
        assert pre in overlays and (pre != a.source or a.independent_batch)
    tag = 'cmmsa_analytic_' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    base = REPO / 'docs/a7-certification-20261003/a9-gcp' / tag
    base.mkdir(parents=True, exist_ok=False)
    (base / 'executed-runner.py').write_bytes(pathlib.Path(__file__).read_bytes())
    RUN_LOG_DIRECTORY = base / (tag + '-local-runtime')
    archive = base / (tag + '.tar.gz')
    script = base / (tag + '.sh')
    with tempfile.TemporaryFile() as raw:
        subprocess.run(['git', 'archive', '--format=tar', 'HEAD', 'lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'], cwd=REPO, stdout=raw, stderr=subprocess.PIPE, timeout=180, check=True, creationflags=subprocess.CREATE_NO_WINDOW)
        raw.seek(0)
        with tarfile.open(fileobj=raw) as old, tarfile.open(archive, 'w:gz') as new:
            for member in old:
                if member.name not in overlays:
                    new.addfile(member, old.extractfile(member) if member.isfile() else None)
            for name, payload in overlays.items():
                item = tarfile.TarInfo(name)
                item.size = len(payload)
                new.addfile(item, io.BytesIO(payload))
    with archive.open('rb') as archive_input:
        archive_sha = hashlib.file_digest(archive_input, 'sha256').hexdigest()
    module = a.source.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
    remote = '''#!/usr/bin/env bash
set -Eeuo pipefail
systemctl is-active --quiet quantyra-idle-shutdown.timer
systemctl is-enabled --quiet quantyra-idle-shutdown.timer
sudo systemd-run --unit=TAG-hard-stop --on-active=18min /sbin/shutdown -h now
mkdir -p /tmp/TAG-evidence
trap 'rc=$?; printf "%s\\n" "$rc" >/tmp/TAG-evidence/native-exit; tar -czf /tmp/TAG-evidence.tar.gz -C /tmp/TAG-evidence .; exit "$rc"' EXIT
echo 'ARCHIVESHA  /tmp/TAG.tar.gz' | sha256sum -c -
WORK="$HOME/TAG"
mkdir "$WORK"
tar -xzf /tmp/TAG.tar.gz -C "$WORK"
cp -al "$HOME/WORKTAG/.lake" "$WORK/.lake"
cd "$WORK"
test "$(git -C .lake/packages/cslib rev-parse HEAD)" = d9be64196bf145edd019f1ccfeaee0c11166ba6b
mkdir -p offline-bin
printf '#!/usr/bin/env bash\ncase "$1" in clone|fetch|pull|ls-remote) echo "Network Git disabled" >&2; exit 93;; esac\nexec /usr/bin/git "$@"\n' >offline-bin/git
chmod +x offline-bin/git
OVERLAYVERIFY
export PATH="$PWD/offline-bin:$HOME/.elan/bin:$PATH"
lean --version >/tmp/TAG-evidence/toolchain.txt
git -C .lake/packages/cslib rev-parse HEAD >/tmp/TAG-evidence/cslib-revision.txt
sha256sum lake-manifest.json lean-toolchain OVERLAYPATHS >/tmp/TAG-evidence/source-before.sha256
rm -f OVERLAYOBJECTS
PREBUILDSTEPS
timeout --signal=TERM --kill-after=20s 900s lake build MODULE >/tmp/TAG-evidence/build.stdout 2>/tmp/TAG-evidence/build.stderr
sha256sum OVERLAYPATHS OVERLAYOBJECTS >/tmp/TAG-evidence/pins.sha256
'''
    prebuild_steps = []
    for index, pre in enumerate(a.prebuild_source):
        pre_module = pre.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
        prebuild_steps.append(
            'set +e\n'
            'timeout --signal=TERM --kill-after=20s 900s lake build ' + pre_module +
            ' >/tmp/TAG-evidence/prebuild-' + str(index) + '.stdout' +
            ' 2>/tmp/TAG-evidence/prebuild-' + str(index) + '.stderr\n'
            'rc=$?\nset -e\n'
            'printf "%s\\n" "$rc" >/tmp/TAG-evidence/prebuild-' + str(index) + '.native-exit\n'
            'if [ "$rc" -ne 0 ]; then exit "$rc"; fi\n'
            'sha256sum ' + pre + ' .lake/build/lib/lean/' + pre.removeprefix('lean/').removesuffix('.lean') +
            '.olean >/tmp/TAG-evidence/prebuild-' + str(index) + '.pins.sha256')
    if a.independent_batch:
        assert len(a.prebuild_source) % 2 == 0
        steps = ['aggregate=0']
        for index, pre in enumerate(a.prebuild_source):
            if index % 2:
                assert pre == a.prebuild_source[index - 1].replace('.lean', 'Checks.lean')
            mod = pre.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
            stem = '/tmp/TAG-evidence/stage-' + str(index)
            command = 'timeout --signal=TERM --kill-after=20s 900s lake build ' + mod + ' >' + stem + '.stdout 2>' + stem + '.stderr'
            prefix = 'set +e\n' if not index % 2 else 'if [ "$source_rc" -eq 0 ]; then\nset +e\n'
            suffix = '\nrc=$?\nset -e\n' if not index % 2 else '\nrc=$?\nset -e\nelse\nrc=125\nprintf "Skipped: corresponding source stage failed\\n" >' + stem + '.skip\nfi\n'
            steps.append(prefix + command + suffix + 'printf "%s\\n" "$rc" >' + stem + '.native-exit\n')
            if not index % 2:
                steps.append('source_rc=$rc\nif [ "$rc" -ne 0 ]; then aggregate=1; fi')
            else:
                steps.append('if [ "$rc" -ne 0 ] && [ "$rc" -ne 125 ]; then aggregate=1; fi')
            obj = '.lake/build/lib/lean/' + pre.removeprefix('lean/').removesuffix('.lean') + '.olean'
            steps.append('if [ "$rc" -eq 0 ]; then sha256sum ' + pre + ' ' + obj + ' >' + stem + '.pins.sha256; fi')
            steps.append('tar -czf /tmp/TAG-evidence.tar.gz.next -C /tmp/TAG-evidence . && mv /tmp/TAG-evidence.tar.gz.next /tmp/TAG-evidence.tar.gz')
        steps.append('printf "%s\\n" "$aggregate" >/tmp/TAG-evidence/aggregate.native-exit\nexit "$aggregate"')
        prebuild_steps = steps
        remote = remote.replace('timeout --signal=TERM --kill-after=20s 900s lake build MODULE >/tmp/TAG-evidence/build.stdout 2>/tmp/TAG-evidence/build.stderr\nsha256sum OVERLAYPATHS OVERLAYOBJECTS >/tmp/TAG-evidence/pins.sha256', '')
    if a.direct_development:
        assert not a.independent_batch
        checks = []
        for pin in a.required_object_pin:
            name, sha = pin.split('=', 1)
            assert name.startswith('.lake/build/lib/lean/') and '..' not in pathlib.PurePosixPath(name).parts
            assert len(sha) == 64 and all(c in '0123456789abcdefABCDEF' for c in sha)
            checks.append("echo '" + sha + '  ' + name + "' | sha256sum -c -")
        capture = 'find .lake/build/lib/lean/PvNP/RealizableHardness -name "*.olean" -type f -print0 | sort -z | xargs -0 sha256sum >/tmp/TAG-evidence/cached-import-objects-before.sha256\n'
        prebuild_steps.insert(0, '\n'.join(checks) + '\n' + capture)
        for index, pre in enumerate(a.prebuild_source):
            mod = pre.removeprefix('lean/').removesuffix('.lean').replace('/', '.')
            obj = '.lake/build/lib/lean/' + pre.removeprefix('lean/').removesuffix('.lean') + '.olean'
            prebuild_steps = [step.replace('lake build ' + mod, 'lake env lean -o ' + obj + ' ' + pre) for step in prebuild_steps]
        remote = remote.replace('lake build MODULE', 'lake env lean -o .lake/build/lib/lean/' + a.source.removeprefix('lean/').removesuffix('.lean') + '.olean ' + a.source)
    remote = remote.replace('PREBUILDSTEPS', '\n'.join(prebuild_steps))
    # Source-only overlays need not be compiled; pin objects only for explicit build stages.
    built_sources = list(overlays)
    overlay_objects = ' '.join('.lake/build/lib/lean/' + name.removeprefix('lean/').removesuffix('.lean') + '.olean*' for name in built_sources)
    overlay_verify = '\n'.join("echo '" + pin + '  ' + name + "' | sha256sum -c -" for name, pin in overlay_pins.items())
    package_capture = r"""
python3 - "$PWD" "$HOME/.elan/bin/lean" /tmp/TAG-evidence <<'PY'
import pathlib,subprocess,hashlib,json,tarfile,os
root=pathlib.Path(__import__('sys').argv[1]); evidence=pathlib.Path(__import__('sys').argv[3])
packages=sorted((root/'.lake/packages').iterdir())
identity={}; sources={}
for p in packages:
    if not p.is_dir(): continue
    if (p/'.git').exists():
        identity[p.name]=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD']).decode().strip()
        patch=subprocess.check_output(['git','-C',str(p),'diff','--binary','HEAD','--'])
        (evidence/(p.name+'-tracked-diff.patch')).write_bytes(patch)
        changed=subprocess.check_output(['git','-C',str(p),'diff','--numstat','HEAD','--']).decode().splitlines()
        for row in changed:
            added,removed,rel=row.split('\t',2)
            if added==removed=='0': continue
            if rel.endswith('.lean'):
                actual=(p/rel).read_bytes().replace(b'\r\n',b'\n')
                canonical=subprocess.check_output(['git','-C',str(p),'show','HEAD:'+rel]).replace(b'\r\n',b'\n')
                assert actual==canonical, ('changed package Lean source',p.name,rel)
    for dirpath,dirs,files in os.walk(p):
        dirs[:]=[d for d in dirs if d not in ['.git','.lake']]
        for f in files:
            if f.endswith('.lean') or f in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
                source=pathlib.Path(dirpath)/f
                sources[str(source.relative_to(root))]=hashlib.sha256(source.read_bytes()).hexdigest()
with tarfile.open(evidence/'package-sources.tar.gz','w:gz') as t:
    for rel in sources: t.add(root/rel,arcname=rel)
(evidence/'package-source-hashes.json').write_text(json.dumps(sources,indent=2))
(evidence/'package-identities.json').write_text(json.dumps(identity,indent=2))
compiler=pathlib.Path(subprocess.check_output([str(pathlib.Path.home()/'.elan/bin/elan'),'which','lean']).decode().strip())
toolchain=compiler.parent.parent
core={}
with tarfile.open(evidence/'core-sources.tar.gz','w:gz') as t:
    for source in sorted((toolchain/'src').rglob('*.lean')):
        rel=str(source.relative_to(toolchain))
        core[rel]=hashlib.sha256(source.read_bytes()).hexdigest()
        t.add(source,arcname=rel)
(evidence/'core-source-hashes.json').write_text(json.dumps(core,indent=2))
(evidence/'compiler-identity.json').write_text(json.dumps({'path':str(compiler),'sha256':hashlib.sha256(compiler.read_bytes()).hexdigest()},indent=2))
subprocess.run(['bash','-c','find "$1/lib/lean" -type f -name "*.olean" -print0 | sort -z | xargs -0 sha256sum','capture',str(toolchain)],stdout=(evidence/'core-object-before.sha256').open('wb'),check=True)
print('PACKAGE_SOURCE_CAPTURE',len(sources))
PY
find .lake/packages -type f -name '*.olean' -print0 | sort -z | xargs -0 sha256sum >/tmp/TAG-evidence/package-object-before.sha256
"""
    package_capture = package_capture.replace('TAG',tag).replace('/tmp/' + tag + '-evidence','/home/dfredriksen_quantyra_org/cmmsa-evidence/' + tag + '-evidence')
    remote = remote.replace('rm -f OVERLAYOBJECTS', package_capture + '\nrm -f OVERLAYOBJECTS')

    for key, value in [('OVERLAYOBJECTS', overlay_objects), ('OVERLAYNAMES', ','.join(overlays)), ('OVERLAYPATHS', ' '.join(overlays)), ('OVERLAYVERIFY', overlay_verify), ('WORKTAG', a.reuse_tag or tag), ('REUSEMODE', 'yes' if a.reuse_tag else 'no'), ('CACHESHA', a.cslib_sha or 'UNUSED_REUSE_CACHE'), ('CACHENAME', cache.name if cache else 'UNUSED_REUSE_CACHE'), ('ARCHIVESHA', archive_sha), ('SOURCESHA', a.expected_sha), ('MODULEPATH', module.replace('.', '/')), ('MODULE', module), ('SOURCE', a.source), ('TAG', tag)]:
        remote = remote.replace(key, value)
    remote = remote.replace('/tmp/' + tag + '-evidence', '/home/dfredriksen_quantyra_org/cmmsa-evidence/' + tag + '-evidence')
    remote = remote.replace('mkdir -p /home/dfredriksen_quantyra_org/cmmsa-evidence/', 'test \"$HOME\" = /home/dfredriksen_quantyra_org\ntest -d \"$HOME\" && test -w \"$HOME\"\nmkdir -p /home/dfredriksen_quantyra_org/cmmsa-evidence/', 1)

    extra_remote = """
sha256sum OVERLAYPATHS >/tmp/TAG-evidence/source-after.sha256
find .lake/build/lib/lean/PvNP -type f -name '*.olean' -print0 | sort -z | xargs -0 sha256sum >/tmp/TAG-evidence/object-after.sha256
printf '%s\n' "$aggregate" >/tmp/TAG-evidence/aggregate.native-exit
exit "$aggregate"
"""
    extra_remote = extra_remote.replace('OVERLAYPATHS', ' '.join(overlays)).replace('TAG', tag)
    extra_remote = extra_remote.replace('/tmp/' + tag + '-evidence', '/home/dfredriksen_quantyra_org/cmmsa-evidence/' + tag + '-evidence')
    remote = remote.replace('exit "$aggregate"', extra_remote)
    import ast
    for block in re.findall(r"<<'PY'\n(.*?)\nPY", remote, re.S): ast.parse(block)
    script.write_text(remote, encoding='utf-8', newline='\n')
    preparation = {'prepared': True, 'archive': str(archive), 'script': str(script),
        'source_sha': a.expected_sha, 'archive_sha': archive_sha, 'execute': a.execute,
        'overlay_pins': overlay_pins, 'dependency_snapshots': snapshots,
        'compiled_prebuild_snapshots': compiled_snapshots,
        'independent_batch': a.independent_batch, 'stage_plan': a.prebuild_source,
        'runner_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    (base / 'preparation.json').write_text(json.dumps(preparation, indent=2), encoding='utf-8')
    print(json.dumps(preparation, indent=2))
    if not a.execute:
        return
    assert cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).strip() == b'TERMINATED'
    started = False
    try:
        cloud(['compute', 'instances', 'start', VM, '--quiet'], 300)
        started = True
        time.sleep(25)
        uploads = [str(archive), str(script)]
        if not a.reuse_tag:
            uploads.append(str(cache))
        cloud(['compute', 'scp'] + uploads + [VM + ':/tmp/', '--quiet', '--tunnel-through-iap'], 300)
        cloud(['compute', 'ssh', VM, '--quiet', '--tunnel-through-iap', '--command=bash /tmp/' + script.name], 1100)
    finally:
        if started:
            try:
                cloud(['compute', 'scp', VM + ':/home/dfredriksen_quantyra_org/cmmsa-evidence/' + tag + '-evidence.tar.gz', str(base / (tag + '-evidence.tar.gz')), '--quiet', '--tunnel-through-iap'], 180)
            finally:
                cloud(['compute', 'instances', 'stop', VM, '--quiet', '--async'], 90)
                for observation in range(20):
                    state = cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).strip()
                    if state == b'TERMINATED': break
                    time.sleep(20)
                else: raise RuntimeError('VM did not reach TERMINATED')
                print('FINAL_VM_STATE', cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).decode().strip())

if __name__ == '__main__':
    try:
        main()
    except BaseException:
        if RUN_LOG_DIRECTORY is not None:
            RUN_LOG_DIRECTORY.mkdir(parents=True, exist_ok=True)
            (RUN_LOG_DIRECTORY / 'wrapper-terminal.json').write_text(json.dumps({
                'wrapper_exit_code': 1, 'traceback': traceback.format_exc(),
                'claim': 'Wrapper outcome only; native proof status is in remote evidence.'
            }, indent=2), encoding='utf-8')
        raise
    else:
        if RUN_LOG_DIRECTORY is not None:
            RUN_LOG_DIRECTORY.mkdir(parents=True, exist_ok=True)
            (RUN_LOG_DIRECTORY / 'wrapper-terminal.json').write_text(json.dumps({
                'wrapper_exit_code': 0,
                'claim': 'Wrapper outcome only; native proof status is in remote evidence.'
            }, indent=2), encoding='utf-8')
