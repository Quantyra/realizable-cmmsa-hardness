"""Freeze same-material export plus one fresh profile, preserving the Full89 capsule."""
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha

PARENT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02')
OUTPUT = PARENT.parent/'full90-material-resource02'
REL = 'lean/PvNP/RealizableHardness/ActualSelectedComplementHC46OriginalApplication.lean'
REQUEST = 'PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication.selected_actual_material_moment_bound_original'
CANDIDATE_SHA = 'C394391645640DEC6E8CE2B701E337ABE091B3F65FCF3E6942A0A958AD0ECA26'
HARNESS = 'fresh-integrated-axioms.lean'


def capsule(path):
    with tarfile.open(path, 'r:gz') as archive:
        members = archive.getmembers()
        if any(not m.isfile() for m in members) or len({m.name for m in members}) != len(members):
            raise RuntimeError('Invalid capsule')
        return {m.name: archive.extractfile(m).read() for m in members}


def validate_expansion(old, new):
    changed = sorted(name for name in old if old[name] != new.get(name))
    if set(old) != set(new) or changed != sorted([REL, HARNESS, 'capture-manifest.json']):
        raise RuntimeError('Unauthorized material successor file scope')
    if sha(new[REL]) != CANDIDATE_SHA:
        raise RuntimeError('Unapproved same-material export')
    if new[HARNESS] != old[HARNESS]+('#print axioms '+REQUEST+'\n').encode():
        raise RuntimeError('Original fresh172 harness changed')
    a = json.loads(old['capture-manifest.json'])
    b = json.loads(new['capture-manifest.json'])
    if len(a['requested_axioms']) != 172 or b['requested_axioms'] != a['requested_axioms']+[REQUEST]:
        raise RuntimeError('Original172 requests or added material profile changed')
    if len(b['project_sources']) != 319 or b['project_sources'][REL]['sha256'] != CANDIDATE_SHA or b['project_sources'][REL]['bytes'] != len(new[REL]):
        raise RuntimeError('Material source manifest mismatch')
    b['project_sources'][REL] = a['project_sources'][REL]
    b['requested_axioms'] = a['requested_axioms']
    if a != b:
        raise RuntimeError('Stages/configuration/compiler/cache/claims boundary drift')
    return changed


def parent_custody():
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    termination = json.loads((check/'vm-termination.json').read_bytes())
    qualified_path = check/'qualified-native'/marker['run']/'successor-native-report.json'
    qualified = json.loads(qualified_path.read_bytes())
    if digest(qualified_path) != '2705033D11D82200894111F915C8FFF04CDF966FB6678B4A67D499A09E43B4B7':
        raise RuntimeError('Qualified native parent changed')
    if terminal['run'] != marker['run'] or not qualified['full_original_A22_HC46_selected_native_gates_green'] or qualified['all_seven_stage_exits'] != [0]*7:
        raise RuntimeError('Full89 native GREEN unproven')
    final = termination['independent']
    if termination['run'] != marker['run'] or not termination['custody_verified_before_stop'] or final['id'] != '7237681467779354904' or final['status'] != 'TERMINATED':
        raise RuntimeError('Parent exact custody/independent termination unproven')
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    return marker, custody


def main():
    marker, custody = parent_custody()
    binding = json.loads((PARENT/'resource-binding.json').read_bytes())
    if digest(PARENT/'input-archive.tar.gz') != binding['files']['input-archive.tar.gz']:
        raise RuntimeError('Parent frozen capsule changed')
    old = capsule(PARENT/'input-archive.tar.gz')
    new = dict(old)
    candidate_path = Path(__file__).with_name('full89-material-consumer-candidate.lean')
    candidate = candidate_path.read_bytes()
    if sha(candidate) != CANDIDATE_SHA:
        raise RuntimeError('Material candidate source drift')
    new[REL] = candidate
    new[HARNESS] += ('#print axioms '+REQUEST+'\n').encode()
    manifest = json.loads(old['capture-manifest.json'])
    manifest['project_sources'][REL].update(sha256=sha(candidate), bytes=len(candidate))
    manifest['requested_axioms'].append(REQUEST)
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    changed = validate_expansion(old, new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'w:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(parent_run=marker['run'], parent_resource=str(PARENT), parent_custody=custody,
                     source=REL, old_sha256=sha(old[REL]), new_sha256=sha(candidate),
                     original172_requests_preserved=True, additional_profile=REQUEST,
                     all_seven_stages_preserved=True, other318_sources_preserved=True,
                     compiler_and_cache_pins_preserved=True, source_derivation_sha256=digest(candidate_path.with_suffix('.json')),
                     local_compilation=False, native_verification_pending=True, accepted=False, launch_clearance=False,
                     full_material_body_review_and_Spectral_numeric_manuscript_gates_open=True)
    (OUTPUT/'source-expansion.json').write_text(json.dumps(expansion, indent=2)+'\n', encoding='utf-8')
    successor = dict(binding, parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
                     source_expansion_sha256=digest(OUTPUT/'source-expansion.json'), changed_files=changed,
                     project_sources_preserved=318, original172_requests_preserved=True,
                     added_request=REQUEST, auxiliary_inputs={name: sha(new[name]) for name in [HARNESS, 'fresh-prior-a7-axioms.lean']},
                     files={name: digest(OUTPUT/name) for name in ['input-archive.tar.gz', 'capture-manifest.json']})
    successor.pop('source_repair_sha256', None)
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'root': str(OUTPUT), 'candidate_sha256': CANDIDATE_SHA, 'requests': 173,
                      'stages': 7, 'input_archive_sha256': digest(OUTPUT/'input-archive.tar.gz'), 'launch_clearance': False}))


if __name__ == '__main__':
    main()
