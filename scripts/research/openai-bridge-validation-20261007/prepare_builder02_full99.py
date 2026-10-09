"""Freeze syntax-only Full99 while preserving full327/192/seven-stage scope."""
import copy
import io
import json
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full98 import OUTPUT as PARENT, REQUESTS, NEW_REQUESTS, MODULES, validate_language

OUTPUT = PARENT.parent / 'full99-matrix-fourier-bullet-repair-resource02'
CANDIDATES = Path(__file__).with_name('full99-matrix-fourier-bullet-repair-v1')
ADDED = ['lean/PvNP/RealizableHardness/BinaryMatrixRightOrbit.lean']

def make_successor(old):
    new = dict(old)
    manifest = json.loads(old['capture-manifest.json'])
    for row in json.loads((CANDIDATES/'derivation.json').read_bytes())['sources']:
        rel = 'lean/PvNP/RealizableHardness/' + row['name']
        data = (CANDIDATES/row['name']).read_bytes()
        assert sha(old[rel]) == row['parent_sha256'] and sha(data) == row['sha256'] and len(data) == row['bytes']
        validate_language(data)
        new[rel] = data
        manifest['project_sources'][rel] = dict(sha256=sha(data), bytes=len(data))
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    validate_expansion(old, new)
    return new

def validate_expansion(old, new):
    assert set(old) == set(new)
    assert sorted(n for n in old if old[n] != new[n]) == sorted(ADDED + ['capture-manifest.json'])
    before, after = old[ADDED[0]], new[ADDED[0]]
    assert before.count(b'\n  - ') == 3
    assert after == before.replace(b'\n  - ', ('\n  '+chr(0xb7)+' ').encode())
    validate_language(after)
    a, b = json.loads(old['capture-manifest.json']), json.loads(new['capture-manifest.json'])
    assert len(a['project_sources']) == len(b['project_sources']) == 327
    assert a['requested_axioms'] == b['requested_axioms'] and len(set(b['requested_axioms'])) == 192
    assert len(a['stages']) == 7
    assert b['project_sources'][ADDED[0]] == dict(sha256=sha(after), bytes=len(after))
    b['project_sources'][ADDED[0]] = a['project_sources'][ADDED[0]]
    assert a == b
    return True

def parent_custody():
    marker = json.loads((PARENT/'launch-once.json').read_bytes()); check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes()); custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '274E5E941CC6502A84299D29CD608457F5F1FE5B2A98593D6C72D24F057321AA'
    assert marker['run'] == terminal['run'] == stop['run']
    assert terminal['terminal']['native_terminal'] and not terminal['terminal']['compile_green']
    assert [r['native_exit'] for r in terminal['terminal']['stages']] == [0,0,0,0,1,125,125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    with tarfile.open(custody['repository_path']) as archive:
        assert json.loads(archive.extractfile('source-before.json').read()) == json.loads(archive.extractfile('source-after.json').read())
        assert archive.extractfile('stage-4.stdout').read().count(b'Unknown identifier `change`') == 2
    return marker, custody

def main():
    from full98_capture_gates import validate_successor
    validate_successor(); marker, custody = parent_custody()
    binding = json.loads((PARENT/'resource-binding.json').read_bytes())
    new = make_successor(capsule(PARENT/'input-archive.tar.gz'))
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = dict(schema='full99-three-bullet-repair-v1', parent_run=marker['run'], parent_custody=custody,
        repaired_sources=ADDED, added_sources=[], all326_other_source_bytes_preserved=True,
        all192_requests_and_seven_stages_preserved=True, exact_inverse_parity=True,
        candidate_derivation_sha256=digest(CANDIDATES/'derivation.json'), compiler_invoked=False,
        native_verification_pending=True, launch_clearance=False, accepted=False)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion, indent=2)+'\n').encode())
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT/'source-expansion.json'), changed_files=ADDED+['capture-manifest.json'],
        added_files=[], project_sources_preserved=326,
        files={n:digest(OUTPUT/n) for n in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(successor, indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz') == new
    print(json.dumps({'root':str(OUTPUT), 'sources':327, 'profiles':192, 'input_sha256':digest(OUTPUT/'input-archive.tar.gz'), 'launch_clearance':False}))

if __name__ == '__main__': main()
