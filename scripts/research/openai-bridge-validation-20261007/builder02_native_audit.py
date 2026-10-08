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

def rebound_owners(original_owners,repair,old_source,new_source,expected_count=13):
    owners=json.loads(json.dumps(original_owners))
    def declaration_line(source,name):
        matches=list(re.finditer(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|public)[ \t]+)*(?:theorem|lemma|def|abbrev)[ \t]+'+re.escape(name)+r'\b',source))
        if len(matches)!=1: raise RuntimeError('Ambiguous/missing requested source declaration')
        return source[:matches[0].start()].count('\n')+1
    changed=[]
    for row in owners['requests']:
        if row['owner_file']!=repair['source']: continue
        name=row['qualified'].rsplit('.',1)[-1]
        if row['current_capture_sha256']!=repair['old_sha256'] or declaration_line(old_source,name)!=row['current_owner_line']:
            raise RuntimeError('Original owner identity mismatch')
        row['current_capture_sha256']=repair['new_sha256']
        row['current_owner_line']=declaration_line(new_source,name)
        changed.append(row['qualified'])
    if len(changed)!=expected_count: raise RuntimeError('Unexpected repaired owner scope')
    return owners

def main(resource_root=None):
    root=Path(resource_root) if resource_root is not None else ROOT
    successor=root.name in ('full84-resource02-warning-clean','full85-resource02','full86-resource02','full87-resource02','full88-resource02')
    if root not in (ROOT,ROOT.parent/'full84-resource02-warning-clean',ROOT.parent/'full85-resource02',ROOT.parent/'full86-resource02',ROOT.parent/'full87-resource02',ROOT.parent/'full88-resource02'): raise RuntimeError('Unexpected resource root')
    repair=None
    if successor:
        if root.name=='full88-resource02':
            from full88_controller import validate_successor
        elif root.name=='full87-resource02':
            from full87_controller import validate_successor
        elif root.name=='full86-resource02':
            from full86_controller import validate_successor
        elif root.name=='full85-resource02':
            from full85_controller import validate_successor
        else:
            from full84_controller import validate_successor
        validate_successor()
        repair=json.loads((root/'source-repair.json').read_bytes())
    marker=json.loads((root/'launch-once.json').read_bytes())
    check=Path(marker['preflight']).resolve(strict=True)
    if not check.is_relative_to((root/'checks').resolve()): raise RuntimeError('Foreign check root')
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
    inner=json.loads((root/'capture-manifest.json').read_bytes())
    original=json.loads((cap/'inputs/capture-manifest.json').read_bytes())
    normalized=json.loads(json.dumps(inner)); normalized['vm']=original['vm']
    changed_sources=[]
    if successor:
        changed_sources=[rel for rel in original['project_sources'] if inner['project_sources'][rel]!=original['project_sources'][rel]]
        expected_files={'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22ParentFactorization.lean'}
        if root.name in ('full86-resource02','full87-resource02','full88-resource02'): expected_files.add('lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22OriginalInduction.lean')
        if set(changed_sources)!=expected_files: raise RuntimeError('Unexpected cumulative repaired source scope')
        for rel in changed_sources:
            normalized['project_sources'][rel]=original['project_sources'][rel]
            manifest['project_sources'][rel]=inner['project_sources'][rel]
    if normalized != original: raise RuntimeError('Capsule differs beyond authorized resource/source binding')
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
    owner_path=HERE/'current-axiom-owner-identities.json'
    owners=json.loads(owner_path.read_bytes())
    if successor:
        with tarfile.open(root/'input-archive.tar.gz','r:gz') as capsule:
            for rel in changed_sources:
                new_source=capsule.extractfile(rel).read().decode('utf-8')
                old_source=(cap/'inputs'/rel).read_text(encoding='utf-8')
                owner_repair=dict(source=rel,old_sha256=original['project_sources'][rel]['sha256'],new_sha256=inner['project_sources'][rel]['sha256'])
                owners=rebound_owners(owners,owner_repair,old_source,new_source,10 if rel.endswith('OriginalInduction.lean') else 13)
        owners['owner_hash_parent_capture']=cap.name
        owners['source_repair_sha256']=digest(root/'source-repair.json')
        c.write_new(run/'resource-current-axiom-owner-identities.json',c.json_bytes(owners))
    load=lambda path:owners if successor and path==owner_path else json.loads(path.read_bytes())
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
        original_capture_preserved=True,only_resource_binding_changed=not successor,source_repair=repair,local_preservation_verified=True,
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
    if successor:
        save(run/'successor-native-report.json',dict(namespace['summary'],resource_capture=root.name,
            parent_capture=cap.name,source_repair_sha256=digest(root/'source-repair.json'),
            rebound_axiom_owner_identities_sha256=digest(run/'resource-current-axiom-owner-identities.json')))
    local_gates(c,m)

if __name__ == '__main__': main()
