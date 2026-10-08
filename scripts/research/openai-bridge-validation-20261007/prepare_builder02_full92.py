"""Immutable import-only repair of the preserved RED Full91 axiom harness."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full91 import OUTPUT as PARENT, REQUESTS

OUTPUT = PARENT.parent / 'full92-source-size-profile-resource02'
HARNESS = 'fresh-integrated-axioms.lean'
MODULES = [
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment',
    'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeOriginalApplication',
]
IMPORTS = ''.join('import ' + module + '\n' for module in MODULES).encode()


def require_added_import_coverage(files):
    manifest = json.loads(files['capture-manifest.json'])
    modules = {rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): rel
               for rel in manifest['project_sources']}
    def imports(data):
        return [name for line in re.findall(r'(?m)^import\s+([^\n]+)', data.decode())
                for name in line.split() if name in modules]
    pending = imports(files[HARNESS])
    reached = set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(imports(files[modules[module]]))
    for request in REQUESTS:
        owner = max((m for m in modules if request.startswith(m + '.')), key=len)
        if owner not in reached:
            raise RuntimeError('Fresh axiom harness does not import added request owner: ' + request)
    return sorted(set(MODULES) & reached)


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
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [r['native_exit'] for r in receipt['terminal']['stages']] == [0] * 6 + [1]
    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        stdout = archive.extractfile('stage-6.stdout').read().decode()
        errors = re.findall(r'^fresh-integrated-axioms\.lean:\d+:\d+: error\(lean\.unknownIdentifier\): Unknown constant `([^`]+)`$', stdout, re.M)
        assert errors == REQUESTS, 'Parent failed outside the exact five missing imports'
        binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
        assert json.loads(archive.extractfile('auxiliary-before.json').read()) == binding['auxiliary_inputs']
        assert json.loads(archive.extractfile('auxiliary-after.json').read()) == binding['auxiliary_inputs']
        manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
        expected = {rel: row['sha256'] for rel, row in manifest['project_sources'].items()}
        expected.update({rel: row['sha256'] for rel, row in manifest['configs'].items()})
        assert json.loads(archive.extractfile('source-before.json').read()) == expected
        assert json.loads(archive.extractfile('source-after.json').read()) == expected
    return marker, custody


def validate_repair(old, new):
    assert set(old) == set(new)
    assert sorted(n for n in old if old[n] != new[n]) == [HARNESS]
    assert new[HARNESS] == IMPORTS + old[HARNESS]
    assert old['capture-manifest.json'] == new['capture-manifest.json']
    assert len(json.loads(new['capture-manifest.json'])['requested_axioms']) == 178
    assert require_added_import_coverage(new) == sorted(MODULES)


def main():
    from full91_capture_gates import validate_successor
    validate_successor()
    marker, custody = parent_custody()
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    for name, pin in binding['files'].items():
        assert digest(PARENT / name) == pin
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = dict(old)
    new[HARNESS] = IMPORTS + old[HARNESS]
    validate_repair(old, new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT / 'input-archive.tar.gz', 'x:gz') as archive:
        for name, data in sorted(new.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion = json.loads((PARENT / 'source-expansion.json').read_bytes())
    expansion.update(schema='full92-import-only-profile-repair-v1',
                     parent_attempt_run=marker['run'], parent_attempt_custody=custody,
                     parent_additive_expansion_sha256=digest(PARENT / 'source-expansion.json'),
                     all322_sources_preserved=True, all178_requests_preserved=True,
                     all_seven_stages_preserved=True, mathematical_statement_changed=False,
                     only_changed_capsule_file=HARNESS, added_imports=MODULES,
                     old_harness_sha256=sha(old[HARNESS]), new_harness_sha256=sha(new[HARNESS]),
                     original_RED_attempt_preserved=True, accepted=False, launch_clearance=False)
    (OUTPUT / 'source-expansion.json').write_text(json.dumps(expansion, indent=2) + '\n', encoding='utf-8')
    successor = copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'),
                     parent_run=marker['run'], source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
                     changed_files=[HARNESS], added_files=[], project_sources_preserved=322,
                     auxiliary_inputs={n: sha(new[n]) for n in binding['auxiliary_inputs']},
                     files={n: digest(OUTPUT / n) for n in ['input-archive.tar.gz', 'capture-manifest.json']})
    (OUTPUT / 'resource-binding.json').write_text(json.dumps(successor, indent=2) + '\n', encoding='utf-8')
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps({'root': str(OUTPUT), 'only_change': HARNESS, 'sources': 322, 'profiles': 178,
                      'input_sha256': digest(OUTPUT / 'input-archive.tar.gz'), 'accepted': False}))


if __name__ == '__main__':
    main()
