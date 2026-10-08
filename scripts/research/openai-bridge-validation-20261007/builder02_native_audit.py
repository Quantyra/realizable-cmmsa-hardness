"""Reuse frozen Full83 qualification thresholds with separately verified VM02 custody."""
import sys
sys.dont_write_bytecode=True
from collections import Counter
import json
from pathlib import Path
import re
import tarfile
from builder02_controller import ROOT, VM, VM_ID, context, local_gates
from custody_checks import digest, verify_local_custody

FINISHER_SHA='AE79CB1B154685AF9DB0E43885225F49C7EB750C5F6F5A8D2B5595ED3EEE7156'

def main():
    marker=json.loads((ROOT/'launch-once.json').read_bytes())
    check=Path(marker['preflight']).resolve(strict=True)
    if not check.is_relative_to((ROOT/'checks').resolve()): raise RuntimeError('Foreign check root')
    receipt=json.loads((check/'terminal-custody.json').read_bytes())
    termination=json.loads((check/'vm-termination.json').read_bytes())
    if receipt['run'] != marker['run'] or termination['run'] != marker['run'] or not termination['custody_verified_before_stop']:
        raise RuntimeError('Custody/termination run mismatch')
    final=termination['independent']
    if final['name'] != VM or str(final['id']) != VM_ID or final['status'] != 'TERMINATED': raise RuntimeError('Independent termination unproven')
    custody=receipt['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    m,runner=context(); c=m['common']; local_gates(c,m)
    HERE=m['HERE']; cap=c.PACKAGE/'captures/capture-full-a22-hc46-83'
    manifest=json.loads((cap/'manifest.json').read_bytes())
    inner=json.loads((ROOT/'capture-manifest.json').read_bytes())
    original=json.loads((cap/'inputs/capture-manifest.json').read_bytes())
    if {**inner,'vm':original['vm']} != original: raise RuntimeError('Capsule differs beyond authorized resource binding')
    finisher=HERE/'finish-native.py'
    if digest(finisher) != FINISHER_SHA: raise RuntimeError('Frozen qualification control drift')
    run=check/'qualified-native'/marker['run']; run.mkdir(parents=True,exist_ok=False)
    d=run/'remote-evidence'; d.mkdir()
    with tarfile.open(custody['repository_path'],'r:gz') as archive:
        members=archive.getmembers()
        if len({member.name for member in members}) != len(members): raise RuntimeError('Duplicate evidence entry')
        for member in members:
            if not member.isfile() or member.name.startswith('/') or any(p in ('','.','..') for p in member.name.split('/')):
                raise RuntimeError('Unsafe evidence entry')
            target=d/member.name; target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as output: output.write(archive.extractfile(member).read())
    load=lambda path:json.loads(path.read_bytes())
    save=lambda path,value:c.write_new(path,c.json_bytes(value))
    expected={name:row['sha256'] for name,row in manifest['project_sources'].items()}
    expected.update({name:row['sha256'] for name,row in manifest['configs'].items()})
    if load(d/'source-before.json') != expected or load(d/'source-after.json') != expected: raise RuntimeError('Compiled source custody failed')
    if load(d/'gcp-execution-identity.json')['id'] != VM_ID: raise RuntimeError('Foreign compiler identity')
    cache=load(d/'verified-cache-provenance.json'); objects=load(d/'object-after.json')
    if cache != inner['cache_provenance']: raise RuntimeError('Cache provenance mismatch')
    comparison={'cache_objects':len(cache['objects']),'changed':[name for name,pin in cache['objects'].items() if objects.get(name)!=pin],
        'compiler_equal':load(d/'compiler-identity.json')==cache['compiler'],
        'packages_equal':load(d/'package-source-hashes.json')==cache['package_sources'],
        'core_equal':load(d/'core-source-hashes.json')==cache['core_sources']}
    if comparison['cache_objects'] != 566 or comparison['changed'] or not all(comparison[name] for name in ['compiler_equal','packages_equal','core_equal']):
        raise RuntimeError('Frozen compiler/cache comparison failed')
    save(run/'cache-comparison.json',comparison)
    save(run/'qualified-resource-preconditions.json',dict(custody=custody,termination=termination,
        original_capture_preserved=True,only_resource_binding_changed=True,local_preservation_verified=True,
        frozen_finisher_sha256=FINISHER_SHA,local_compilation=False))
    text=finisher.read_text()
    tail=text[text.index('baseline=load('):]
    replacements={"save(HERE/'native-report.json',summary)":"save(run/'native-report.json',summary)",
                  "c.write_new(HERE/'native-report.md',":"c.write_new(run/'native-report.md',"}
    for old,new in replacements.items():
        if tail.count(old)!=1: raise RuntimeError('Unexpected frozen output binding')
        tail=tail.replace(old,new)
    c.write_new(run/'executed-original-finisher.py',finisher.read_bytes())
    c.write_new(run/'executed-qualified-tail.py',tail.encode())
    namespace=dict(Counter=Counter,json=json,re=re,c=c,m=m,HERE=HERE,run=run,cap=cap,manifest=manifest,d=d,
                   load=load,save=save,cache=cache,objects=objects,final=final,custody=custody)
    # The original warning seals, owner pins, 172 profiles, object closure and
    # green criterion are executed unchanged; only two output paths are rebound.
    exec(compile(tail,str(finisher)+'::resource02-qualification','exec'),namespace)
    local_gates(c,m)

if __name__ == '__main__': main()
