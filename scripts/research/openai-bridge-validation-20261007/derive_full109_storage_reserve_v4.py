"""Exclude the older unstructured Full89 qualification; preserve the failed v3 check."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'compress_full109_settled_graphs_v3.py'
    assert digest(source) == '66F803B5A8B4CDB57332404AE08515A2F0C530620136D80FFB9426C4C69D6E54'
    assert not (HERE / 'full109-settled-graphs-lossless-compression-v3').exists()
    observation = dict(schema='full109-storage-v3-original-tool-observation-v1',
        original_tool_chunk='a045d5', original_native_exit=1, source_sha256=digest(source),
        error_type='FileNotFoundError',
        missing='C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification/qualification-summary.json',
        failure_before_compression_or_record_creation=True,
        complete_raw_command_output_available_in_original_tool_receipt=True,
        this_file_is_a_structured_observation_not_a_raw_output_copy=True,
        original_control_preserved=True, no_compiler_or_cloud_operation=True)
    (HERE / 'full109-storage-reserve-v3-observation.json').open('x', encoding='utf-8').write(json.dumps(observation, indent=2)+'\n')
    replacements = [
        ("('full89-resource02', 'consumption-v2', 'qualification'), ", ''),
        ('full109-settled-graphs-lossless-compression-v3', 'full109-settled-graphs-lossless-compression-v4'),
        ('full109-settled-graph-lossless-storage-v3', 'full109-settled-graph-lossless-storage-v4')]
    value = source.read_text(encoding='utf-8')
    for old, new in replacements:
        assert value.count(old) == 1
        value = value.replace(old, new)
    ast.parse(value)
    target = HERE / 'compress_full109_settled_graphs_v4.py'
    target.open('xb').write(value.encode('utf-8'))
    record = dict(source=str(source), source_sha256=digest(source), target=str(target),
                  target_sha256=digest(target), replacements=replacements,
                  qualification_stop_and_byte_guards_retained=True, no_deletion=True)
    (HERE / 'full109-storage-reserve-derivation-v4.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
