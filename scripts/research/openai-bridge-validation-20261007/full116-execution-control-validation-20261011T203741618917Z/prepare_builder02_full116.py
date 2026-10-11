"""Freeze the one-source Full115 GL selected-row inverse and cardinality repair, retaining full369/full347/seven stages."""
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from full116_gl_repair_structure_v1 import validate as validate_structure
from prepare_builder02_full115 import OUTPUT as PARENT

HERE = Path(__file__).resolve().parent
OUTPUT = PARENT.parent / 'full116-exact-real-complex-operators-repair6-resource02'
CAPTURES = [
    ('full116-selected-rows-repair-capture-v1', 'BBB0D74FE058CF51175C9CC8785CBEF91B9ED394BF9EEB3AECE5FC9BB34FBBDA', 'RectangularGLSelectedRows.lean'),
]


def repairs():
    result = []
    for folder, pin, filename in CAPTURES:
        base = HERE / folder
        assert digest(base / 'index.json') == pin
        index = json.loads((base / 'index.json').read_bytes())
        for row in index['files']:
            path = base / row['copy']
            assert path.resolve(strict=True).is_relative_to(base.resolve())
            assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
        source = base / filename
        assert digest(source) == index['new_sha256']
        result.append((index['source'], source.read_bytes(), index, pin))
    return result


def validate_expansion(old, new):
    rows = repairs()
    changes = {row[0] for row in rows}
    assert set(old) == set(new)
    assert {name for name in old if old[name] != new[name]} == changes | {'capture-manifest.json'}
    before = json.loads(old['capture-manifest.json'])
    after = json.loads(new['capture-manifest.json'])
    normalized = copy.deepcopy(after)
    for name, data, index, pin in rows:
        assert new[name] == data and hashlib.sha256(old[name]).hexdigest().upper() == index['old_sha256']
        validate_structure(old[name], data)
        text = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
        assert not re.search(r'(?m)^\s*set_option linter\.', text)
        assert re.findall(r'(?m)^import .+$', old[name].decode()) == re.findall(r'(?m)^import .+$', text)
        assert after['project_sources'][name] == dict(sha256=index['new_sha256'], bytes=len(data))
        normalized['project_sources'][name] = before['project_sources'][name]
    assert normalized == before
    assert len(after['project_sources']) == 369 and len(after['requested_axioms']) == 347 and len(after['stages']) == 7
    assert len(new) == 376
    return True


def main():
    from full115_capture_gates import validate_successor
    validate_successor()
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert marker['run'] == terminal['run'] == stop['run'] == 'cmmsa_a8_output_20261011T201326Z_31fcd86a'
    assert terminal['terminal']['native_terminal'] and not terminal['terminal']['compile_green']
    assert [row['native_exit'] for row in terminal['terminal']['stages']] == [0, 0, 0, 0, 1, 125, 125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    old = capsule(PARENT / 'input-archive.tar.gz')
    new = dict(old)
    manifest = json.loads(old['capture-manifest.json'])
    repaired = []
    for name, data, index, pin in repairs():
        new[name] = data
        manifest['project_sources'][name] = dict(sha256=index['new_sha256'], bytes=len(data))
        repaired.append(dict(path=name, old_sha256=index['old_sha256'], new_sha256=index['new_sha256'],
            bytes=len(data), immutable_repair_index_sha256=pin))
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode('utf-8')
    validate_expansion(old, new)
    assert shutil.disk_usage(PARENT).free >= 1536 * 1024**2 + 2 * sum(len(data) for data in new.values())
    OUTPUT.mkdir(exist_ok=False)
    with (OUTPUT / 'input-archive.tar.gz').open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as archive:
                for name, data in sorted(new.items()):
                    member = tarfile.TarInfo(name)
                    member.size = len(data)
                    member.mode = 0o644
                    archive.addfile(member, io.BytesIO(data))
    (OUTPUT / 'capture-manifest.json').open('xb').write(new['capture-manifest.json'])
    expansion = dict(schema='full116-full369-full347-gl-selected-row inverse and cardinality-repair-v1',
        parent_run=marker['run'], parent_custody=custody,
        parent_terminal_sha256=digest(check / 'terminal-custody.json'),
        parent_historical_stop_sha256=digest(check / 'vm-termination.json'),
        parent_native_report_sha256=digest(check / 'qualified-native' / marker['run'] / 'native-report.json'),
        parent_failed_original_audit_preserved=True, repaired_sources=repaired, added_sources=[],
        all368_other_source_bytes_preserved=True, all347_requests_and7_stage_commands_preserved=True,
        all_existing_declaration_headers_and_imports_preserved=True,
        exactly_two_reviewed_private_helpers_added=True,
        default_heartbeat_cap_unchanged_at200000=True,
        compiler_invoked=False, native_verification_pending=True, launch_clearance=False, accepted=False, full_goal_complete=False)
    (OUTPUT / 'source-expansion.json').open('x', encoding='utf-8').write(json.dumps(expansion, indent=2)+'\n')
    binding = json.loads((PARENT / 'resource-binding.json').read_bytes())
    binding.update(parent_resource_binding_sha256=digest(PARENT / 'resource-binding.json'), parent_run=marker['run'],
        source_expansion_sha256=digest(OUTPUT / 'source-expansion.json'),
        changed_files=[row['path'] for row in repaired] + ['capture-manifest.json'], added_files=[],
        project_sources_preserved=368,
        files={name:digest(OUTPUT / name) for name in ('input-archive.tar.gz', 'capture-manifest.json')})
    (OUTPUT / 'resource-binding.json').open('x', encoding='utf-8').write(json.dumps(binding, indent=2)+'\n')
    assert capsule(OUTPUT / 'input-archive.tar.gz') == new
    print(json.dumps(dict(root=str(OUTPUT), sources=369, profiles=347, stages=7, members=376,
        input_sha256=digest(OUTPUT / 'input-archive.tar.gz'), manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
        binding_sha256=digest(OUTPUT / 'resource-binding.json'), launch_clearance=False)), flush=True)


if __name__ == '__main__':
    main()
