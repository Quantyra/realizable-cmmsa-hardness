"""Derive complete trace controls only from actual qualified Full108 custody."""
import ast
import json
import re
import sys
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full108 import OUTPUT

HERE = Path(__file__).parent
NAMES = [
    'full107_consumption_v3_controller.py',
    'full107_consumption_v3_worker.py',
    'stage_full107_consumption_v3.py',
    'terminate_full107_consumption_v3.py',
    'qualify_full107_consumption_v3.py',
    'test_full107_consumption_v3_gates.py',
]


def main(write=False):
    marker = json.loads((OUTPUT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    report = check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    qualified = json.loads(report.read_bytes())
    assert marker['run'] == receipt['run'] == stop['run']
    assert receipt['terminal']['compile_green']
    assert qualified['full108_expanded_native_gates_green']
    assert qualified['expanded_requested_axiom_count'] == 261
    assert qualified['project_closure_sources'] == 348
    assert qualified['owned_warning_headers'] == qualified['inherited_regression_headers'] == [0]*7
    assert qualified['cache_objects_unchanged'] == 566
    assert stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == '7237681467779354904'
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    with tarfile.open(custody['repository_path']) as archive:
        objects = json.loads(archive.extractfile('object-after.json').read())
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
    expected = {'.lake/build/lib/lean/'+p.removeprefix('lean/').removesuffix('.lean')+'.olean'
                for p in manifest['project_sources']}
    assert len(expected) == 348 and expected <= set(objects)
    assert len(objects) == 703  # Parent699 plus two complete olean/ilean pairs.
    rows = []
    for source in NAMES:
        target = source.replace('full107', 'full108')
        text = (HERE/source).read_text(encoding='utf8')
        text = text.replace('full107-exact-product-energy-repair', 'full108-exact-crosslevel-product')
        text = text.replace('full107', 'full108').replace('Full107', 'Full108')
        text = text.replace('cmmsa_a8_output_20261010T053442Z_835bc942', marker['run'])
        text = text.replace('835bc942', marker['run'].rsplit('_', 1)[1])
        for before, after in [('346', '348'), ('260', '261'), ('699', '703'), ('92', '93')]:
            text = re.sub(r'\b'+before+r'\b', after, text)
        text = text.replace('exact260', 'exact261').replace('focused-ninety-two-consumer', 'focused-ninety-three-consumer')
        text = text.replace('from prepare_full106_product_energy_scope import additions as SPECTRAL_ADDITIONS',
                            'from prepare_full108_crosslevel_product_scope import additions as SPECTRAL_ADDITIONS')
        ast.parse(text)
        path = HERE/target
        data = text.encode()
        if write:
            path.open('xb').write(data)
        else:
            assert path.read_bytes() == data
        rows.append(dict(source=source, source_sha256=digest(HERE/source), target=target, target_sha256=digest(path)))
    result = dict(schema='full108-actual-qualified-consumption-control-derivation-v3', records=rows,
                  run=marker['run'], native_archive_sha256=custody['remote_sha256'], qualified_report_sha256=digest(report),
                  project_sources=348, actual_native_object_entries=703, requested_roots=261, focused_consumers=93,
                  parent_trace_algorithms_and_resource_source_object_dependency_guards_preserved=True,
                  compiler_invoked=False, probe_executed=False, accepted=False)
    path = HERE/'full108-consumption-control-derivation-v3.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if write:
        path.open('xb').write(data)
    else:
        assert path.read_bytes() == data
    print(json.dumps(dict(controls=6, run=marker['run'], roots=261, focused=93, objects=703)))


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
