"""Local capture/control only; compiler commands are remote script text."""
from pathlib import Path
import hashlib, json, re, subprocess, sys, runpy

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
src = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9FiberCount.lean'
chk = src.replace('.lean', 'Checks.lean')
offered = {src: '168B8929AA6EE8555D13526552036E7267388F59A8F78C1F885E725D8A79BABD',
    'docs/a7-certification-20261003/a9-author-report.md': 'C94830BDC549219E49133D6DD37361153AFCD4AFBBB8F879013BCF97255E987F'}
assert all(sha((root/p).read_bytes()) == h for p,h in offered.items())
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=root).strip()
records = {}; external = set()
def capture(module):
    rel = 'lean/' + module.replace('.', '/') + '.lean'
    if rel in records: return
    path = root/rel
    if not path.exists():
        assert not module.startswith('PvNP.'), module
        external.add(module); return
    data = path.read_bytes()
    records[rel] = {'sha256':sha(data),'bytes':len(data)}
    dest = out/'inputs'/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
    for line in re.findall(r'^import\s+([^\r\n]+)',data.decode('utf-8-sig'),re.M):
        for dep in line.split('--')[0].split(): capture(dep)
capture(src.removeprefix('lean/').removesuffix('.lean').replace('/','.'))
name = 'PvNP.RealizableHardness.ActualBinaryMatrixHC46A9FiberCount.a9_fixed_final_graph_census'
checks = ('import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9FiberCount\n'
    '#check '+name+'\n#print '+name+'\n#print axioms '+name+'\n').encode()
dest = out/'inputs'/chk; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(checks)
records[chk] = {'sha256':sha(checks),'bytes':len(checks)}
config = {}
for rel in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    data = (root/rel).read_bytes(); archived = subprocess.check_output(['git','show','HEAD:'+rel],cwd=root)
    assert data.replace(b'\r\n',b'\n') == archived.replace(b'\r\n',b'\n'), rel
    (out/'inputs'/rel).write_bytes(data)
    config[rel] = {'captured_sha256':sha(data),'archive_sha256':sha(archived),'normalized_equal':True}
for args,filename in [(['git','status','--porcelain=v1','-unormal'],'status-before.txt'),
    (['git','rev-parse','HEAD','origin/main'],'heads-before.txt')]:
    (out/filename).write_bytes(subprocess.check_output(args,cwd=root))
(out/'manifest.json').write_text(json.dumps({'offer':offered,'sources':records,
    'external_imports':sorted(external),'config':config,'local_compilation':False},indent=2))
code = (out.parent/'cloud-closure-runner.py').read_text()
start = code.index('    # Third stage verifies')
end = code.index("    script.write_text(remote", start)
extra = '''    extra_remote = """
sha256sum OVERLAYPATHS >/tmp/TAG-evidence/source-after.sha256
find .lake/build/lib/lean/PvNP -type f -name '*.olean' -print0 | sort -z | xargs -0 sha256sum >/tmp/TAG-evidence/object-after.sha256
printf '%s\\n' "$aggregate" >/tmp/TAG-evidence/aggregate.native-exit
exit "$aggregate"
"""
    extra_remote = extra_remote.replace('OVERLAYPATHS', ' '.join(overlays)).replace('TAG', tag)
    extra_remote = extra_remote.replace('/tmp/' + tag + '-evidence', '/home/dfredriksen_quantyra_org/cmmsa-evidence/' + tag + '-evidence')
    remote = remote.replace('exit "$aggregate"', extra_remote)
'''
code = code[:start]+extra+code[end:]
# Reuse the package/build cache only. Every source comes from the new archive in
# a unique workspace, so unrelated source edits in the old warm workspace cannot
# create a custody failure or enter this build.
old_start = code.index('WORK="$HOME/WORKTAG"')
old_end = code.index('cd "$WORK"\ntest "$(git -C .lake/packages/cslib',old_start)
code = code[:old_start]+'''WORK="$HOME/TAG"
mkdir "$WORK"
tar -xzf /tmp/TAG.tar.gz -C "$WORK"
cp -al "$HOME/WORKTAG/.lake" "$WORK/.lake"
'''+code[old_end:]
code = code.replace("REPO / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment/durable-runs' / tag", "REPO / 'docs/a7-certification-20261003/a9-gcp' / tag")
code = code.replace("built_sources = list(dict.fromkeys([*a.prebuild_source, a.source]))", "built_sources = list(overlays)")
code = code.replace("'.olean' for name in built_sources)", "'.olean*' for name in built_sources)")
code = code.replace("                cloud(['compute', 'instances', 'stop', VM, '--quiet'], 300)",
    "                cloud(['compute', 'instances', 'stop', VM, '--quiet', '--async'], 90)\n"
    "                for observation in range(20):\n"
    "                    state = cloud(['compute', 'instances', 'describe', VM, '--format=value(status)']).strip()\n"
    "                    if state == b'TERMINATED': break\n"
    "                    time.sleep(20)\n"
    "                else: raise RuntimeError('VM did not reach TERMINATED')")
# Every captured project object is invalidated; external package sources and objects are
# captured on GCP before compilation, with tracked package source cleanliness verified.
insert = r'''    package_capture = r"""
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
'''
code = code.replace("    for key, value in [('OVERLAYOBJECTS'", insert+"\n    for key, value in [('OVERLAYOBJECTS'")
code = code.replace("    script.write_text(remote, encoding='utf-8', newline='\\n')",
    "    import ast\n"
    "    for block in re.findall(r\"<<'PY'\\n(.*?)\\nPY\", remote, re.S): ast.parse(block)\n"
    "    script.write_text(remote, encoding='utf-8', newline='\\n')")
(out/'runner.py').write_text(code,encoding='utf-8')
args = [str(out/'runner.py'),'--source',src,'--expected-sha',records[src]['sha256'],
    '--reuse-tag','cmmsa_analytic_20261003T231858Z','--independent-batch',
    '--prebuild-source',src,'--prebuild-source',chk,'--execute']
for rel,row in records.items():
    if rel == src: continue
    args += ['--dependency-source',rel,'--dependency-sha',row['sha256'],
        '--prebuild-snapshot' if rel==chk else '--dependency-snapshot',
        rel+'='+str((out/'inputs'/rel).relative_to(root))]
(out/'invocation.json').write_text(json.dumps(args,indent=2))
print('CAPTURE_ACK',len(records),'project modules, source',records[src]['sha256'],flush=True)
sys.argv=args
runpy.run_path(str(out/'runner.py'),run_name='__main__')
