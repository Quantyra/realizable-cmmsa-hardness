"""Immutable final-let delimiter repair; preserve Full94 scope and guards."""
import copy
import io
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full94 import OUTPUT as PARENT

OUTPUT = PARENT.parent / 'full95-manuscript-moment-syntax-repair-resource02'
SOURCE = 'lean/PvNP/RealizableHardness/ActualSelectedComplementManuscriptDyadicMoment.lean'
OLD = b'    let fc := coordinateFunctional I copies U A f\n'
NEW = b'    let fc := coordinateFunctional I copies U A f;\n'


def parent_custody():
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert receipt['run'] == stop['run'] == marker['run']
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == 'C3AC112E83E4042551CEACDA550416454B1391D01115D6E3E69AA5C3059524D5'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [s['native_exit'] for s in receipt['terminal']['stages']] == [0, 0, 0, 0, 1, 125, 125]
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        def read(name):
            return json.loads(archive.extractfile(name).read())
        terminal = read('dedicated-worker-terminal.json')
        assert terminal['native_exits'] == {'begin': 0, 'compile': 1, 'finish': 0}
        assert terminal['failure'] is None and not terminal['accepted']
        assert terminal['run'] == marker['run'] and terminal['host']['id'] == '7237681467779354904'
        text = archive.extractfile('stage-4.stdout').read().decode()
        errors = [line for line in text.splitlines() if line.startswith('error: lean/')]
        assert errors == [
            'error: ' + SOURCE + ":239:61: expected ';' or line break",
            'error: ' + SOURCE + ":363:61: expected ';' or line break",
        ], 'Parent failed beyond the exact final-let syntax regression'
        expected = {rel: row['sha256'] for rel, row in manifest['project_sources'].items()}
        expected.update({rel: row['sha256'] for rel, row in manifest['configs'].items()})
        assert read('source-before.json') == read('source-after.json') == expected
        assert read('auxiliary-before.json') == read('auxiliary-after.json') == binding['auxiliary_inputs']
        cache, objects = manifest['cache_provenance'], read('object-after.json')
        assert read('verified-cache-provenance.json') == cache
        assert len(cache['objects']) == 566 and all(objects.get(rel) == pin for rel, pin in cache['objects'].items())
        for name, key in [('compiler-identity.json', 'compiler'), ('package-source-hashes.json', 'package_sources'), ('core-source-hashes.json', 'core_sources')]:
            assert read(name) == cache[key]
    return marker, custody


def make_successor(old):
    assert old[SOURCE].count(OLD) == 2
    new = dict(old)
    new[SOURCE] = old[SOURCE].replace(OLD, NEW)
    manifest = json.loads(old['capture-manifest.json'])
    manifest['project_sources'][SOURCE] = {'sha256': sha(new[SOURCE]), 'bytes': len(new[SOURCE])}
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    validate_repair(old, new)
    return new


def validate_repair(old, new):
    assert set(old) == set(new)
    assert sorted(n for n in old if old[n] != new[n]) == sorted([SOURCE, 'capture-manifest.json'])
    assert old[SOURCE].count(OLD) == 2 and new[SOURCE] == old[SOURCE].replace(OLD, NEW)
    assert new[SOURCE].replace(NEW, OLD) == old[SOURCE]
    a, b = json.loads(old['capture-manifest.json']), json.loads(new['capture-manifest.json'])
    assert len(b['project_sources']) == 323 and len(b['requested_axioms']) == 181
    assert b['project_sources'][SOURCE] == {'sha256': sha(new[SOURCE]), 'bytes': len(new[SOURCE])}
    b['project_sources'][SOURCE] = a['project_sources'][SOURCE]
    assert b == a, 'Unauthorized profile/stage/config/compiler/cache or source change'


def main():
    from full94_capture_gates import validate_successor
    validate_successor()
    marker, custody = parent_custody()
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = make_successor(old)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = {
        'schema': 'full95-two-final-let-delimiters-repair-v1', 'parent_run': marker['run'],
        'parent_custody': custody, 'changed_source': SOURCE,
        'old_source_sha256': sha(old[SOURCE]), 'new_source_sha256': sha(new[SOURCE]),
        'added_sources': [], 'additional_profiles': [],
        'all181_requests_preserved': True, 'all_seven_stages_preserved': True,
        'parent322_source_bytes_preserved': True, 'original319_source_bytes_preserved': True,
        'all_mathematical_statements_and_contract_guards_preserved': True,
        'exact_inverse_source_byte_parity': True, 'harness_compiler_cache_configs_preserved': True,
        'original_failed_attempt_preserved': True, 'local_compilation': False,
        'native_verification_pending': True, 'launch_clearance': False, 'accepted': False,
    }
    (OUTPUT / 'source-expansion.json').write_text(json.dumps(expansion, indent=2) + '\n', encoding='utf-8')
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'),
                     parent_run=marker['run'], source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                     changed_files=[SOURCE, 'capture-manifest.json'], added_files=[],
                     project_sources_preserved=322,
                     files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    # Retain the three dyadic additional-profile names consumed by the Linux
    # verifier, as well as every one of the 181 manifest requests.
    (OUTPUT / 'resource-binding.json').write_text(json.dumps(successor, indent=2) + '\n', encoding='utf-8')
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps({'root': str(OUTPUT), 'sources': 323, 'profiles': 181,
                      'input_sha256': digest(OUTPUT / 'input-archive.tar.gz'),
                      'launch_clearance': False, 'accepted': False}))


if __name__ == '__main__':
    main()
