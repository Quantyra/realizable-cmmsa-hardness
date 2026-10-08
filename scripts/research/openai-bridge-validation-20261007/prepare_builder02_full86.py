"""Freeze explicit induction elaboration/arithmetic repairs from failed Full85."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest,verify_local_custody
from prepare_builder02 import sha

PARENT=Path('C:/Users/dfred/.quantyra/builder02/full85-resource02')
OUTPUT=PARENT.parent/'full86-resource02'
REL='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22OriginalInduction.lean'

def main():
    marker=json.loads((PARENT/'launch-once.json').read_bytes()); check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes()); custody=terminal['custody']
    if terminal['run']!=marker['run'] or terminal['terminal']['stages'][4]['native_exit']!=1: raise RuntimeError('Required parent failure missing')
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    binding=json.loads((PARENT/'resource-binding.json').read_bytes())
    if digest(PARENT/'input-archive.tar.gz')!=binding['files']['input-archive.tar.gz']: raise RuntimeError('Parent capsule drift')
    with tarfile.open(PARENT/'input-archive.tar.gz','r:gz') as archive:
        members=archive.getmembers()
        if any(not m.isfile() for m in members) or len({m.name for m in members})!=len(members): raise RuntimeError('Invalid parent capsule')
        files={m.name:archive.extractfile(m).read() for m in members}
    before=dict(files); manifest=json.loads(files['capture-manifest.json']); source=files[REL].decode('utf-8')
    if REL not in manifest['owned_sources'] or REL in manifest['cache_provenance']['project_sources']: raise RuntimeError('Repair outside owned scope')
    edits={
      '  have hsupport := complexRankProjection_supportedThrough le_rfl f\n':
      '  have hsupport := complexRankProjection_supportedThrough (i := j) (D := j) le_rfl f\n',
      '    have hpm : p = 2 * m := hpEven\n    nlinarith\n':
      '    have hpm : p = 2 * m := hpEven\n    have hmm : m ≤ m * m := by\n      simpa only [Nat.mul_one] using Nat.mul_le_mul_left m (show 1 ≤ m by omega)\n    have hbound : m - 1 ≤ m ^ 2 := by\n      simpa only [pow_two] using (Nat.sub_le m 1).trans hmm\n    rw [hpm]\n    calc\n      _ ≤ 200 * j ^ 2 * (2 * m) ^ 2 + (10 * j ^ 2) * m ^ 2 :=\n        Nat.add_le_add_left (Nat.mul_le_mul_left (10 * j ^ 2) hbound) _\n      _ = 810 * (j ^ 2 * m ^ 2) := by ring\n      _ ≤ 840 * (j ^ 2 * m ^ 2) := Nat.mul_le_mul_right _ (by decide)\n      _ = _ := by ring\n',
      '  have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hj\n  nlinarith\n':
      '  have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hj\n  have hsq : (j - 1) ^ 2 + j ≤ j ^ 2 := by\n    calc\n      _ = (j - 1) ^ 2 + (j - 1) + 1 := by omega\n      _ ≤ (j - 1 + 1) ^ 2 := by nlinarith\n      _ = j ^ 2 := by rw [hsub]\n  have hlinear : 6 * j ≤ 500 * j * p := by\n    calc\n      _ ≤ 500 * j := Nat.mul_le_mul_right j (by decide)\n      _ ≤ 500 * j * p := by\n        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (500 * j) (show 1 ≤ p by omega)\n  calc\n    _ ≤ 500 * (j - 1) ^ 2 * p + 500 * j * p := Nat.add_le_add_left hlinear _\n    _ = 500 * ((j - 1) ^ 2 + j) * p := by ring\n    _ ≤ _ := Nat.mul_le_mul_right p (Nat.mul_le_mul_left 500 hsq)\n',
      '        intro bound hE hB A H T hcost\n':
      '        intro bound hE hB A H T hcost\n        change a12Energy A H (complexRankProjection level g) T ≤ bound\n',
      '          intro A H T hcost\n          rw [a22_zero_cost_energy A H T _ (by omega)]\n':
      '          intro A H T hcost\n          change a12Energy A H (complexRankProjection 0 g) T ≤ E\n          have hcost\' : Module.finrank F A + Module.finrank F (W n\' ⧸ H) ≤ 0 := hcost\n          rw [a22_zero_cost_energy A H T _ (by omega)]\n',
      '        intro A H T hcost\n        rw [a22_zero_cost_energy A H T _ (by omega)]\n':
      '        intro A H T hcost\n        change a12Energy A H (complexRankProjection 0 g) T ≤ (2 : Real) ^ (500 * 0 ^ 2 * p) * eta ^ 2\n        have hcost\' : Module.finrank F A + Module.finrank F (W n\' ⧸ H) ≤ 0 := hcost\n        rw [a22_zero_cost_energy A H T _ (by omega)]\n',
      '            omega\n          exact hclose _ hfinal hB\n':
      '            exact Nat.mul_le_mul_right p\n              (Nat.mul_le_mul_right (level ^ 2) (by decide : 420 ≤ 500))\n          exact hclose _ hfinal hB\n'}
    for old,new in edits.items():
        if source.count(old)!=1: raise RuntimeError('Unexpected repair anchor: '+old[:80])
        source=source.replace(old,new)
    files[REL]=source.encode('utf-8'); row=manifest['project_sources'][REL]; row['sha256']=sha(files[REL])
    if 'bytes' in row: row['bytes']=len(files[REL])
    if 'origin' in row: row['origin']='Full85 native induction errors: explicit indices, energy forms and arithmetic monotonicity'
    files['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    changed=sorted(name for name in files if files[name]!=before[name])
    if changed!=sorted([REL,'capture-manifest.json']): raise RuntimeError('Unexpected successor changes')
    for rel,pin in manifest['project_sources'].items():
        if sha(files[rel])!=pin['sha256']: raise RuntimeError('Source pin mismatch')
    OUTPUT.mkdir(parents=True,exist_ok=False)
    with tarfile.open(OUTPUT/'input-archive.tar.gz','w:gz') as archive:
        for name,data in sorted(files.items()):
            m=tarfile.TarInfo(name); m.size=len(data); m.mode=0o644; archive.addfile(m,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(files['capture-manifest.json'])
    repair=dict(parent_run=marker['run'],parent_resource=str(PARENT),parent_custody=custody,source=REL,
      old_sha256=sha(before[REL]),new_sha256=sha(files[REL]),exact_edits=edits,other_project_sources_preserved=318,
      stages_preserved=True,axiom_requests_preserved=True,compiler_and_cache_pins_preserved=True,
      native_verification_pending=True,launch_clearance=False,local_compilation=False)
    (OUTPUT/'source-repair.json').write_text(json.dumps(repair,indent=2)+'\n')
    successor=dict(binding,parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],
      source_repair_sha256=digest(OUTPUT/'source-repair.json'),changed_files=changed,
      files={name:digest(OUTPUT/name) for name in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor,indent=2)+'\n')
    print(json.dumps(dict(source=REL,new_sha256=repair['new_sha256'],repair_edits=len(edits),launch_clearance=False),indent=2))

if __name__=='__main__': main()
