"""Reuse frozen Full83 qualification thresholds with separately verified VM02 custody."""
import sys
sys.dont_write_bytecode=True
from collections import Counter
import json
from pathlib import Path
import re
import tarfile
from full98_builder02_controller import ROOT, VM, VM_ID, context, local_gates
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
    if root != ROOT: raise RuntimeError('Unexpected material resource root')
    successor=True
    from full98_capture_gates import validate_successor
    validate_successor()
    additive=json.loads((root/'source-expansion.json').read_bytes())
    from prepare_builder02_full91 import PARENT, REQUESTS as SOURCE_REQUESTS
    from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS
    from prepare_builder02_full98 import REQUESTS as BRIDGE_REQUESTS
    REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS
    repair=json.loads((PARENT/'source-expansion.json').read_bytes())
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
    additive = dict(additive)
    additive['added_sources'] = sorted(set(inner['project_sources']) - set(original['project_sources']))
    if len(additive['added_sources']) != 8: raise RuntimeError('Incomplete cumulative additive source scope')
    normalized=json.loads(json.dumps(inner)); normalized['vm']=original['vm']
    changed_sources=[]
    if successor:
        changed_sources=[rel for rel in original['project_sources'] if inner['project_sources'][rel]!=original['project_sources'][rel]]
        expected_files={'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22ParentFactorization.lean'}
        if root.name in ('full86-resource02','full87-resource02','full88-resource02','full89-resource02','full98-actual-matrix-fourier-bridge-resource02'): expected_files.add('lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22OriginalInduction.lean')
        if root.name in ('full89-resource02','full98-actual-matrix-fourier-bridge-resource02'): expected_files.add('lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46OriginalExactInhabitant.lean')
        expected_files.add('lean/PvNP/RealizableHardness/ActualSelectedComplementHC46OriginalApplication.lean')
        if inner['requested_axioms'] != original['requested_axioms']+[repair['additional_profile']]+REQUESTS: raise RuntimeError('Added material profile scope mismatch')
        normalized['requested_axioms']=original['requested_axioms']
        normalized['stages'][4]=original['stages'][4]
        for rel in additive['added_sources']:
            normalized['project_sources'].pop(rel)
            manifest['project_sources'][rel]=inner['project_sources'][rel]
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
                count=2 if rel.endswith('OriginalApplication.lean') else (6 if rel.endswith('OriginalExactInhabitant.lean') else (10 if rel.endswith('OriginalInduction.lean') else 13))
                owners=rebound_owners(owners,owner_repair,old_source,new_source,count)
        owners['owner_hash_parent_capture']=cap.name
        owners['source_expansion_sha256']=digest(root/'source-expansion.json')
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
    m=dict(m)
    m['OWNED']=list(m['OWNED'])+additive['added_sources']
    text=finisher.read_text()
    tail=text[text.index('baseline=load('):]
    replacements={"save(HERE/'native-report.json',summary)":"save(run/'native-report.json',summary)",
                  "c.write_new(HERE/'native-report.md',":"c.write_new(run/'native-report.md',"}
    for old,new in replacements.items():
        if tail.count(old)!=1: raise RuntimeError('Unexpected frozen output binding')
        tail=tail.replace(old,new)
    c.write_new(run/'executed-original-finisher.py',finisher.read_bytes())
    c.write_new(run/'executed-qualified-tail.py',tail.encode())
    # The frozen capture has no additive source paths. Supply only those
    # missing reads from separately hash-verified immutable successor inputs.
    overlay = run/'additive-capture-source-overlay'
    overlay.mkdir()
    with tarfile.open(root/'input-archive.tar.gz','r:gz') as inputs:
        for rel in additive['added_sources']:
            data = inputs.extractfile(rel).read()
            import hashlib
            if hashlib.sha256(data).hexdigest().upper() != inner['project_sources'][rel]['sha256']:
                raise RuntimeError('Additive capture overlay source drift')
            path = overlay/rel
            path.parent.mkdir(parents=True,exist_ok=True)
            with path.open('xb') as output: output.write(data)
    class InputReads:
        def __truediv__(self,rel):
            return overlay/rel if str(rel) in additive['added_sources'] else cap/'inputs'/rel
    class CaptureReads:
        name = cap.name
        def __truediv__(self,rel):
            return InputReads() if str(rel) == 'inputs' else cap/rel
    save(run/'additive-capture-read-binding.json',dict(original_capture=str(cap),
         added_source_sha256={rel:inner['project_sources'][rel]['sha256'] for rel in additive['added_sources']},
         original_capture_modified=False, original_finisher_tail_modified=False))
    namespace=dict(Counter=Counter,json=json,re=re,c=c,m=m,HERE=HERE,run=run,cap=CaptureReads(),manifest=manifest,d=d,
                   load=load,save=save,cache=cache,objects=objects,final=final,custody=custody)
    # The original warning seals, owner pins, 172 profiles, object closure and
    # green criterion are executed unchanged; only two output paths are rebound.
    exec(compile(tail,str(finisher)+'::resource02-qualification','exec'),namespace)
    if successor:
        save(run/'successor-native-report.json',dict(namespace['summary'],resource_capture=root.name,
            parent_capture=cap.name,source_expansion_sha256=digest(root/'source-expansion.json'),
            rebound_axiom_owner_identities_sha256=digest(run/'resource-current-axiom-owner-identities.json')))
    profiles=c.axiom_profiles((d/'stage-6.stdout').read_text(encoding='utf-8'))
    extra_requests=[repair['additional_profile']]+REQUESTS
    extra_profiles={request:profiles.get(request) for request in extra_requests}
    extra_bad=any(value is None or not set(value) <= c.STANDARD_AXIOMS for value in extra_profiles.values())
    added_objects={rel:'.lake/build/lib/lean/'+rel.removeprefix('lean/').removesuffix('.lean')+'.olean' for rel in additive['added_sources']}
    if any(objects.get(obj) is None for obj in added_objects.values()): raise RuntimeError('Added source object missing')
    binding=load(root/'resource-binding.json')
    auxiliary_equal=load(d/'auxiliary-before.json') == load(d/'auxiliary-after.json') == binding['auxiliary_inputs']
    expanded=dict(namespace['summary'], resource_capture=root.name, original_requested_axioms=172,
                  added_requested_axioms=extra_requests, expanded_requested_axiom_count=192,
                  additional_profiles=extra_profiles, material_export_bad_or_missing_axioms=extra_bad,
                  fresh_auxiliary_inputs_preserved=auxiliary_equal,
                  full98_expanded_native_gates_green=namespace['summary']['full_original_A22_HC46_selected_native_gates_green'] and not extra_bad and auxiliary_equal,
                  material_body_review_complete=False, consumption_trace_complete=False,
                  Spectral47_numeric_and_full_manuscript_gates_open=True, accepted=False)
    expanded.update(added_project_sources=additive['added_sources'], added_object_hashes={rel:objects[obj] for rel,obj in added_objects.items()}, original173_requests_preserved=True, source_row_independence_native_verified=not extra_bad, manuscript_dyadic_consumer_native_verified=not extra_bad, numeric_NO_proven=False)
    expanded.update(added_source_object_identities=[dict(source_path=rel, source_sha256=inner['project_sources'][rel]['sha256'], compiled_object_path=obj, compiled_object_sha256=objects[obj]) for rel,obj in added_objects.items()], legacy_source_keyed_object_hash_field_retained_for_compatibility=True, explicit_contract_bridges_and_right_orbit_helper_native_verified=not extra_bad, actual_matrix_right_orbit_and_Fourier_covariance_native_verified=not extra_bad, universal_Spectral47_inhabitant_proven=False)
    save(run/'material-expanded-native-report.json',expanded)
    print(json.dumps(expanded,indent=2))
    local_gates(c,m)

if __name__ == '__main__': main()
