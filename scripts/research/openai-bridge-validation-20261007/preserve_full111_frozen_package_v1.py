"""Preserve the offline two-source repair package and its successful control checks."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from prepare_builder02_full111 import OUTPUT, CAPTURES, validate_expansion, PARENT
from prepare_builder02_full90 import capsule

HERE = Path(__file__).resolve().parent


def main():
    validation = HERE / 'full111-execution-control-validation-20261011T031402428924Z'
    result = json.loads((validation / 'result.json').read_bytes())
    assert all(row['native_exit'] == 0 for row in result['commands'])
    assert 'Ran 16 tests' in (validation / '1.stderr').read_text(encoding='utf-8')
    assert (validation / '1.stderr').read_text(encoding='utf-8').rstrip().endswith('OK')
    for number, row in enumerate(result['commands']):
        for stream in ('stdout', 'stderr'):
            assert digest(validation / f'{number}.{stream}') == row[stream + '_sha256']
    for name, pin in result['source_snapshots'].items():
        assert digest(HERE / name) == digest(validation / name) == pin
    old, new = capsule(PARENT / 'input-archive.tar.gz'), capsule(OUTPUT / 'input-archive.tar.gz')
    validate_expansion(old, new)
    files = [OUTPUT / name for name in ('input-archive.tar.gz', 'capture-manifest.json', 'source-expansion.json', 'resource-binding.json')]
    assert not (OUTPUT / 'launch-once.json').exists()
    target = HERE / 'full111-immutable-package-record-v1'
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in files) >= 1536 * 1024**2
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for path in files:
        copy = target / path.name
        with path.open('rb') as source, copy.open('xb') as destination:
            shutil.copyfileobj(source, destination)
        assert digest(copy) == digest(path)
        rows.append(dict(original=str(path), copy=copy.name, bytes=path.stat().st_size, sha256=digest(path)))
    value = dict(schema='full111-frozen-two-source-repair-and-control-checks-v1', files=rows,
        immutable_repair_captures=[dict(folder=folder, index_sha256=pin, source=source) for folder, pin, source in CAPTURES],
        original_preparation_tool_handle=41254, original_preparation_exit=0,
        preparation_raw_tool_stream_archive_claimed=False,
        original_validation_tool_handle=98666, original_validation_exit=0,
        validation_result=str(validation / 'result.json'), validation_result_sha256=digest(validation / 'result.json'),
        package_member_count=len(new), sources=369, requests=347, stages=7,
        all367_other_sources_and_all_checks_and_harness_and_stage_commands_unchanged=True,
        complete_offline_scope_and_sixteen_synthetic_tests_passed=True,
        no_local_Lean_invoked=True, no_GCP_compiler_invoked=True, launch_clearance=False, accepted=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), original_files=len(rows), input_sha256=digest(OUTPUT / 'input-archive.tar.gz'), index_sha256=digest(target / 'index.json'))), flush=True)


if __name__ == '__main__':
    main()
