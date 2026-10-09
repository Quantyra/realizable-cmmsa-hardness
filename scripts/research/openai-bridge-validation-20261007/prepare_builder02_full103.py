"""Freeze the evidence-bound one-argument repair; never compile locally."""
import copy
import io
import json
import re
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from prepare_builder02_full102 import OUTPUT as PARENT, REQUESTS

HERE = Path(__file__).parent
REPAIRS = HERE / 'full102-owned-warning-repair-candidate-v1'
OUTPUT = PARENT.parent / 'full103-spectral-owned-warning-repair-resource02'
SOURCE = 'lean/PvNP/RealizableHardness/ActualFiniteAppendImageTailBridge.lean'


def headers(data):
    text = data.decode()
    starts = list(re.finditer(r'(?m)^(?:(?:private|noncomputable|protected) )*(?:theorem|lemma|def|instance|abbrev)\b', text))
    return [text[m.start():text.index(':=', m.start())] for m in starts]


def validate_expansion(old, new):
    repair = json.loads((REPAIRS/'derivation.json').read_bytes())
    assert repair['source'] == SOURCE
    assert set(old) == set(new)
    assert {p for p in old if old[p] != new[p]} == {SOURCE, 'capture-manifest.json'}
    before, after = old[SOURCE], new[SOURCE]
    assert before.count(b'simp [hcol]') == 1
    assert after == before.replace(b'simp [hcol]', b'simp', 1)
    assert after == (REPAIRS/SOURCE).read_bytes()
    assert headers(before) == headers(after)
    assert not re.search(r'(?m)^\s*set_option linter\.', after.decode())
    a = json.loads(old['capture-manifest.json'])
    b = json.loads(new['capture-manifest.json'])
    assert len(b['project_sources']) == 340 and len(b['requested_axioms']) == 251 and len(b['stages']) == 7
    assert a['project_sources'][SOURCE]['sha256'] == repair['old_sha256']
    assert b['project_sources'][SOURCE] == dict(sha256=repair['new_sha256'], bytes=len(after))
    assert digest(REPAIRS/SOURCE) == repair['new_sha256']
    normal = copy.deepcopy(b)
    normal['project_sources'][SOURCE] = a['project_sources'][SOURCE]
    assert normal == a, 'Only the single proof source pin may change'
    return True


def main():
    from full102_capture_gates import validate_successor
    validate_successor()
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    c = terminal['custody']
    verify_local_custody(c['short_path'], c['repository_path'], c['remote_sha256'], c['bytes'])
    stop = json.loads((check/'vm-termination.json').read_bytes())
    assert stop['run'] == marker['run'] == terminal['run'] and terminal['terminal']['compile_green']
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == '7237681467779354904'
    q = check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    report = json.loads(q.read_bytes())
    assert not report['full102_expanded_native_gates_green']
    assert report['owned_warning_headers'] == [0,0,0,0,1,1,0]
    assert report['inherited_regression_headers'] == [0]*7 and report['bad_profiles'] == report['missing_objects'] == 0
    repair = json.loads((REPAIRS/'derivation.json').read_bytes())
    assert repair['parent_run'] == marker['run']
    old = capsule(PARENT/'input-archive.tar.gz')
    new = dict(old)
    new[SOURCE] = (REPAIRS/SOURCE).read_bytes()
    manifest = json.loads(old['capture-manifest.json'])
    manifest['project_sources'][SOURCE] = dict(sha256=repair['new_sha256'], bytes=len(new[SOURCE]))
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    validate_expansion(old, new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name); member.size=len(data); member.mode=0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = json.loads((PARENT/'source-expansion.json').read_bytes())
    expansion.update(schema='full103-full340-full251-owned-warning-repair-v1', parent_run=marker['run'],
        parent_custody=c, parent_qualified_report_sha256=digest(q), parent_qualified_green=False,
        parent_warning_hold_retained=True, repaired_sources=[dict(path=SOURCE, original_sha256=repair['old_sha256'],
        sha256=repair['new_sha256'], bytes=len(new[SOURCE]), all_declaration_headers_preserved=True,
        no_linter_disable_added=True)], repair_derivation_sha256=digest(REPAIRS/'derivation.json'),
        parent_capture_sources=340, parent_capture_profiles=251, added_sources=[], additional_profiles=[],
        all340_source_paths_and251_profiles_and7_stage_commands_preserved=True,
        all339_other_source_bytes_preserved=True, compiler_invoked=False, native_verification_pending=True,
        launch_clearance=False, accepted=False)
    expansion.pop('all332_other_source_bytes_preserved', None)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion, indent=2)+'\n').encode())
    binding = json.loads((PARENT/'resource-binding.json').read_bytes())
    binding.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'), changed_files=[SOURCE, 'capture-manifest.json'],
        added_files=[], files={name:digest(OUTPUT/name) for name in ('input-archive.tar.gz','capture-manifest.json')})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(binding, indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=340, profiles=251,
        input_sha256=digest(OUTPUT/'input-archive.tar.gz'), manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
        launch_clearance=False)))


if __name__ == '__main__': main()
