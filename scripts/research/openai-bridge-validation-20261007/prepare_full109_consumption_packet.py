"""Rebind identical complete348/full261/focused93 tooling; no cloud or Lean."""
import json
import shutil
from custody_checks import digest
from prepare_builder02_full108 import OUTPUT as PARENT
from prepare_builder02_full109 import OUTPUT


def main():
    from full109_capture_gates import validate_successor
    validate_successor()
    parent = PARENT/'consumption-preparation-v1-dag'
    old = json.loads((parent/'readiness.json').read_bytes())
    assert digest(parent/'tooling.tar.gz') == old['tooling_archive_sha256']
    a, b = [json.loads((root/'capture-manifest.json').read_bytes()) for root in [PARENT, OUTPUT]]
    assert list(a['project_sources']) == list(b['project_sources'])
    assert a['requested_axioms'] == b['requested_axioms']
    assert (old['project_modules_exact'], old['requested_roots_exact'], old['focused_consumers_exact']) == (348, 261, 93)
    for name, row in old['files'].items():
        assert digest(parent/name) == row['sha256'] and (parent/name).stat().st_size == row['bytes']
    root = OUTPUT/'consumption-preparation-v1-dag'
    root.mkdir()
    for name in ['tooling.tar.gz', *old['files']]:
        shutil.copyfile(parent/name, root/name)
        assert digest(root/name) == digest(parent/name)
    result = dict(old, schema='full109-identical-complete261-focused93-tooling-v1',
                  parent_tooling_archive_sha256=old['tooling_archive_sha256'],
                  capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
                  input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),
                  identical_probe_and_postprocess_bytes=True, identical_postprocess_bytes=True,
                  all348_parent_modules_261_roots_93_focus_preserved=True,
                  native_qualification_pending=True, probe_executed=False, launch_clearance=False, accepted=False)
    with (root/'readiness.json').open('x', encoding='utf8') as stream:
        stream.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(tooling_sha256=result['tooling_archive_sha256'], modules=348, roots=261, focused=93,
                          identical_probe_and_postprocess_bytes=True, probe_executed=False)))


if __name__ == '__main__':
    main()
