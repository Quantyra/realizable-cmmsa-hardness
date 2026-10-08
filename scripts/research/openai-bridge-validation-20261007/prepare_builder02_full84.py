"""Freeze a syntax-only successor from verified failed Full83 evidence; no compiler."""
import io
import json
from pathlib import Path
import tarfile
import sys
from builder02_controller import ROOT
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha

OUTPUT=ROOT.parent/'full84-resource02'
REL='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A22ParentFactorization.lean'

def main(warning_clean=False):
    output=ROOT.parent/'full84-resource02-warning-clean' if warning_clean else OUTPUT
    marker=json.loads((ROOT/'launch-once.json').read_bytes())
    check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes())
    if terminal['run'] != marker['run'] or terminal['terminal']['stages'][4]['native_exit'] != 1:
        raise RuntimeError('Required parent stage-4 failure missing')
    custody=terminal['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    binding=json.loads((ROOT/'resource-binding.json').read_bytes())
    if digest(ROOT/'input-archive.tar.gz') != binding['files']['input-archive.tar.gz']: raise RuntimeError('Parent capsule drift')
    with tarfile.open(ROOT/'input-archive.tar.gz','r:gz') as archive:
        members=archive.getmembers()
        if any(not member.isfile() for member in members) or len({m.name for m in members}) != len(members): raise RuntimeError('Unsafe parent capsule')
        files={member.name:archive.extractfile(member).read() for member in members}
    before=dict(files); manifest=json.loads(files['capture-manifest.json'])
    if REL not in manifest['owned_sources'] or REL in manifest['cache_provenance']['project_sources']:
        raise RuntimeError('Repair is outside owned source scope or alters cached dependencies')
    source=files[REL].decode('utf-8')
    edits={"  rw [Submodule.comap_bot, hker, finrank_bot, houter'] at hadd\n":
           "  rw [Submodule.comap_bot, hker, finrank_bot, houter'] at hadd\n  simp only [finrank_bot, zero_add] at hadd\n",
           '    rw [finrank_bot, hQdim]\n    change Module.finrank F':
           '    rw [finrank_bot, hQdim, zero_add]\n    change Module.finrank F'}
    if warning_clean:
        edits.update({'    change Module.finrank F (A.map C.mkQ) +\n      Module.finrank F (U ⧸ Q) ≤ j - 1\n':'',
                      '    change Module.finrank F (H ⧸ Q0) ≤ j - 1\n':''})
    for old,new in edits.items():
        if source.count(old) != 1: raise RuntimeError('Unexpected proof repair anchor')
        source=source.replace(old,new)
    files[REL]=source.encode('utf-8')
    row=manifest['project_sources'][REL]
    row['sha256']=sha(files[REL])
    if 'bytes' in row: row['bytes']=len(files[REL])
    if 'origin' in row: row['origin']='Full83 native failure: private syntax-only finrank/zero-add simplification repair'
    files['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    changed=sorted(name for name in files if files[name] != before[name])
    if changed != sorted([REL,'capture-manifest.json']): raise RuntimeError('Unapproved successor change')
    for rel,pin in manifest['project_sources'].items():
        if sha(files[rel]) != pin['sha256']: raise RuntimeError('Successor source pin mismatch')
    output.mkdir(parents=True,exist_ok=False)
    with tarfile.open(output/'input-archive.tar.gz','w:gz') as archive:
        for name,data in sorted(files.items()):
            member=tarfile.TarInfo(name); member.size=len(data); member.mode=0o644
            archive.addfile(member,io.BytesIO(data))
    (output/'capture-manifest.json').write_bytes(files['capture-manifest.json'])
    repair=dict(parent_run=marker['run'],parent_custody=custody,source=REL,old_sha256=sha(before[REL]),
                new_sha256=sha(files[REL]),exact_edits=edits,other_project_sources_preserved=len(manifest['project_sources'])-1,
                stages_preserved=True,axiom_requests_preserved=True,compiler_and_cache_pins_preserved=True,
                local_compilation=False,native_verification_pending=True,launch_clearance=False)
    repair['warning_clean']=warning_clean
    (output/'source-repair.json').write_text(json.dumps(repair,indent=2)+'\n')
    successor=dict(binding,parent_resource_binding_sha256=digest(ROOT/'resource-binding.json'),parent_run=marker['run'],
                   source_repair_sha256=digest(output/'source-repair.json'),changed_files=changed,
                   project_sources_preserved=len(manifest['project_sources'])-1,
                   files={name:digest(output/name) for name in ['input-archive.tar.gz','capture-manifest.json']},
                   helper_sha256=sha(files['cloud_capture.py']),launch_clearance=False)
    (output/'resource-binding.json').write_text(json.dumps(successor,indent=2)+'\n')
    print(json.dumps(repair,indent=2))

if __name__ == '__main__':
    if sys.argv[1:] not in ([],['--warning-clean']): raise SystemExit('Default immutable capsule or --warning-clean')
    main(sys.argv[1:] == ['--warning-clean'])
