"""Preserve Full84 and freeze an explicit mapped-bottom rewrite before mean transport."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest,verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full84 import REL

PARENT=Path('C:/Users/dfred/.quantyra/builder02/full84-resource02-warning-clean')
OUTPUT=PARENT.parent/'full85-resource02'

def main():
    marker=json.loads((PARENT/'launch-once.json').read_bytes())
    check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes())
    if terminal['run']!=marker['run'] or terminal['terminal']['stages'][4]['native_exit']!=1: raise RuntimeError('Required failed parent missing')
    custody=terminal['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    binding=json.loads((PARENT/'resource-binding.json').read_bytes())
    if digest(PARENT/'input-archive.tar.gz')!=binding['files']['input-archive.tar.gz']: raise RuntimeError('Parent capsule drift')
    with tarfile.open(PARENT/'input-archive.tar.gz','r:gz') as archive:
        members=archive.getmembers()
        if any(not m.isfile() for m in members) or len({m.name for m in members})!=len(members): raise RuntimeError('Invalid parent capsule')
        files={m.name:archive.extractfile(m).read() for m in members}
    before=dict(files); manifest=json.loads(files['capture-manifest.json'])
    source=files[REL].decode('utf-8')
    anchor='  have hMeanTransport : a18UniformMean (fun N => Complex.normSq (complexCarrierAffineRestrict Z H\n'
    replacement=('  have hZmap : Z.map Z.mkQ = (⊥ : Submodule F (V d ⧸ Z)) := by\n'
                 '    simp only [Z, Submodule.map_bot]\n'
                 '  rw [hZmap] at hc\n'+anchor)
    if source.count(anchor)!=1: raise RuntimeError('Unexpected transport repair anchor')
    files[REL]=source.replace(anchor,replacement).encode('utf-8')
    row=manifest['project_sources'][REL]; row['sha256']=sha(files[REL])
    if 'bytes' in row: row['bytes']=len(files[REL])
    if 'origin' in row: row['origin']='Full84 native type mismatch: explicit mapped-bottom rewrite before Fintype mean transport'
    files['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    changed=sorted(name for name in files if files[name]!=before[name])
    if changed!=sorted([REL,'capture-manifest.json']): raise RuntimeError('Unexpected successor changes')
    for rel,pin in manifest['project_sources'].items():
        if sha(files[rel])!=pin['sha256']: raise RuntimeError('Source pin mismatch')
    OUTPUT.mkdir(parents=True,exist_ok=False)
    with tarfile.open(OUTPUT/'input-archive.tar.gz','w:gz') as archive:
        for name,data in sorted(files.items()):
            m=tarfile.TarInfo(name); m.size=len(data); m.mode=0o644
            archive.addfile(m,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(files['capture-manifest.json'])
    repair=dict(parent_run=marker['run'],parent_resource=str(PARENT),parent_custody=custody,source=REL,
        old_sha256=sha(before[REL]),new_sha256=sha(files[REL]),exact_edits={anchor:replacement},
        other_project_sources_preserved=318,stages_preserved=True,axiom_requests_preserved=True,
        compiler_and_cache_pins_preserved=True,native_verification_pending=True,launch_clearance=False,local_compilation=False)
    (OUTPUT/'source-repair.json').write_text(json.dumps(repair,indent=2)+'\n')
    successor=dict(binding,parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],
        source_repair_sha256=digest(OUTPUT/'source-repair.json'),changed_files=changed,
        files={name:digest(OUTPUT/name) for name in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor,indent=2)+'\n')
    print(json.dumps(repair,indent=2))

if __name__=='__main__': main()
