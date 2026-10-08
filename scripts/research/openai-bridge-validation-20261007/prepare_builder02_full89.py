"""Preserve Full88 and freeze two HC46 proof-body repairs; no Lean execution."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha

PARENT = Path('C:/Users/dfred/.quantyra/builder02/full88-resource02')
OUTPUT = PARENT.parent/'full89-resource02'
REL = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46OriginalExactInhabitant.lean'
EDITS = {
    '      500 * i ^ 2 * p ^ 2 := by nlinarith\n': '''      500 * i ^ 2 * p ^ 2 := by
    have hm2 : 2 * m ≤ p := by omega
    have hmp := Nat.mul_le_mul_left (5 * i ^ 2 + 250 * i ^ 2 * p) hm2
    have hpp : p ≤ p ^ 2 := by nlinarith
    have hsmall := Nat.mul_le_mul_left (5 * i ^ 2) hpp
    calc
      _ = 200 * i ^ 2 * p ^ 2 + (5 * i ^ 2 + 250 * i ^ 2 * p) * (2 * m) := by ring
      _ ≤ 200 * i ^ 2 * p ^ 2 + (5 * i ^ 2 + 250 * i ^ 2 * p) * p :=
        Nat.add_le_add_left hmp _
      _ = 450 * i ^ 2 * p ^ 2 + 5 * i ^ 2 * p := by ring
      _ ≤ 450 * i ^ 2 * p ^ 2 + 5 * i ^ 2 * p ^ 2 := Nat.add_le_add_left hsmall _
      _ = 455 * (i ^ 2 * p ^ 2) := by ring
      _ ≤ 500 * (i ^ 2 * p ^ 2) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring
''',
    '''      simp [rankProjection, fourierCoeff, uniformMean, lpMoment, lpNorm,
        Real.zero_rpow (by positivity : (1 / (p : Real)) ≠ 0)]
''': '''      simp [rankProjection, fourierCoeff, uniformMean, lpMoment, lpNorm]
      rw [zero_pow (by omega : p ≠ 0),
        Real.zero_rpow (by positivity : (p : Real)⁻¹ ≠ 0)]
'''
}

def main():
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    terminal = json.loads((Path(marker['preflight'])/'terminal-custody.json').read_bytes())
    custody = terminal['custody']
    if terminal['run'] != marker['run'] or terminal['terminal']['stages'][4]['native_exit'] != 1:
        raise RuntimeError('Required parent failure absent')
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    binding = json.loads((PARENT/'resource-binding.json').read_bytes())
    if digest(PARENT/'input-archive.tar.gz') != binding['files']['input-archive.tar.gz']:
        raise RuntimeError('Parent capsule drift')
    with tarfile.open(PARENT/'input-archive.tar.gz') as archive:
        members = archive.getmembers()
        if any(not m.isfile() for m in members) or len({m.name for m in members}) != len(members):
            raise RuntimeError('Invalid parent capsule')
        files = {m.name: archive.extractfile(m).read() for m in members}
    before = dict(files)
    manifest = json.loads(files['capture-manifest.json'])
    source = files[REL].decode('utf-8')
    for old, new in EDITS.items():
        if source.count(old) != 1:
            raise RuntimeError('Unexpected repair anchor')
        source = source.replace(old, new)
    files[REL] = source.encode('utf-8')
    manifest['project_sources'][REL].update(sha256=sha(files[REL]), bytes=len(files[REL]))
    files['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    changed = sorted(name for name in files if files[name] != before[name])
    if changed != sorted((REL, 'capture-manifest.json')):
        raise RuntimeError('Unexpected successor changes')
    if any(sha(files[rel]) != row['sha256'] for rel, row in manifest['project_sources'].items()):
        raise RuntimeError('Source pin mismatch')
    OUTPUT.mkdir(exist_ok=False)
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'w:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(files['capture-manifest.json'])
    repair = dict(parent_run=marker['run'], parent_resource=str(PARENT), parent_custody=custody,
        source=REL, old_sha256=sha(before[REL]), new_sha256=sha(files[REL]), exact_edits=EDITS,
        other_project_sources_preserved=318, stages_preserved=True, axiom_requests_preserved=True,
        compiler_and_cache_pins_preserved=True, native_verification_pending=True, launch_clearance=False, local_compilation=False)
    (OUTPUT/'source-repair.json').write_text(json.dumps(repair, indent=2)+'\n', encoding='utf-8')
    successor = dict(binding, parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
        source_repair_sha256=digest(OUTPUT/'source-repair.json'), changed_files=changed,
        files={name: digest(OUTPUT/name) for name in ('input-archive.tar.gz', 'capture-manifest.json')})
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(source=REL, new_sha256=repair['new_sha256'], repair_edits=len(EDITS), launch_clearance=False)))

if __name__ == '__main__':
    main()
