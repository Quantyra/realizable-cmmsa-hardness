"""Read-only independent custody/input/receipt audit; no local formal execution."""
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile

REPO = Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ARCHIVE_SHA = '5250C27279B656A4DD9A1289523426AF46526087DED5AF840D5C4A4091BE385C'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    custody = json.loads(Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp/upstream-seven-native-profile-custody-2026-10-08.json').read_bytes())
    for name in ('short_copy','second_copy'):
        data = Path(custody[name]).read_bytes()
        assert len(data)==2039396 and sha(data)==ARCHIVE_SHA
    with tarfile.open(custody['short_copy']) as archive:
        names = [m.name for m in archive.getmembers()]
        assert len(names)==len(set(names))
        def read(name):
            member=archive.getmember(name); assert member.isfile()
            return archive.extractfile(member).read()
        capture=read('input-archive.tar.gz')
        assert sha(capture)=='59F78711916A8F6B805253180872D4BB0D53D0648C7B15E111D00221ED393BC7'
        with tarfile.open(fileobj=io.BytesIO(capture)) as frozen:
            manifest_bytes=frozen.extractfile('selected-capture-manifest.json').read()
            assert sha(manifest_bytes)=='D7644716119D88259AAEEC01DD6412760E5B2BE1B0243AE7E041E6C08E655267'
            manifest=json.loads(manifest_bytes)
            assert manifest['commit']==COMMIT
            inputs={}
            for name,pin in manifest['files'].items():
                body=frozen.extractfile(name).read()
                assert len(body)==pin['bytes'] and sha(body)==pin['sha256']
                inputs[name]=body
        assert read('selected-capture-manifest.json')==manifest_bytes
        assert read('selected-upstream-axioms.lean')==inputs['selected-upstream-axioms.lean']
        paths=[p for p in inputs if p!='selected-upstream-axioms.lean']
        raw=subprocess.check_output(['git','-C',str(REPO),'cat-file','--batch'],
            input=''.join(COMMIT+':'+p+'\n' for p in paths).encode())
        stream=io.BytesIO(raw)
        for path in paths:
            header=stream.readline().decode().strip().split()
            assert len(header)==3 and header[1]=='blob'
            assert stream.read(int(header[2]))==inputs[path]
            assert stream.read(1)==b'\n'
        assert not stream.read()
        packages=json.loads(inputs['lean/lake-manifest.json'])['packages']
        staging=json.loads(read('package-staging-receipt.json'))
        assert len(packages)==len(staging['checkouts'])==42
        for p in packages:
            row=next(r for r in staging['checkouts'] if r['name']==p['name'].strip('«»'))
            assert row['revision']==p['rev'] and row['origin']==p['url'] and row['clean_before_patch']
        patches=staging['compatibility_patches']; assert len(patches)==23
        for p in patches:
            assert p['reverse_check'] and sha(inputs['lean/patches/'+p['patch']])==p['sha256']
        commands=json.loads(read('package-staging-commands.json'))
        assert len(commands)==363 and all(r['native_exit']==0 for r in commands)
        for folder in ('original-selected-build-v2','original-selected-profiles-v1'):
            assert read(folder+'/native-exit.txt').strip()==b'0'
        build=json.loads(read('original-selected-build-v2/command.json'))
        assert build['argv'][1:]==['--no-cache','build',*manifest['roots']]
        assert 'version 4.34.1,' in build['version'] and '5045d0056413266e57c625dcd7c365b10e377c52' in build['version']
        stdout=read('original-selected-profiles-v1/stdout.txt').decode()
        profiles=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout)
        assert len(profiles)==7 and set(n for n,a in profiles)==set(manifest['requested_axiom_profiles'])
        assert all(set(a.strip() for a in ax.split(','))=={'propext','Classical.choice','Quot.sound'} for n,ax in profiles)
        assert sha(read('run_original_upstream_build_linux.py'))=='983AC9D33DE6CB9480078C821D2B231600D501CA13B88B542DD8D3425C67251C'
        result=dict(schema='original-upstream-bounded-evidence-post-audit-v1',
            archive_sha256=ARCHIVE_SHA,two_copy_custody=True,original_git_blobs_matched=len(paths),
            frozen_inputs_matched=len(inputs),package_pins=42,verified_patch_receipts=23,
            staging_commands_native_zero=363,build_native_exit=0,profile_native_exit=0,exact_standard_profiles=7,
            bounded_evidence_audit_passed=True,remote_postrun_source_object_hash_inventory_present=False,
            whole_library_certified=False,cmmsa_bridge_verified=False,accepted=False)
    destination=Path('C:/Users/dfred/.quantyra/upstream/original-native-profiles-custody-v1/post-audit-v1.json')
    with destination.open('x',encoding='utf-8') as output:
        json.dump(result,output,indent=2);output.write('\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
