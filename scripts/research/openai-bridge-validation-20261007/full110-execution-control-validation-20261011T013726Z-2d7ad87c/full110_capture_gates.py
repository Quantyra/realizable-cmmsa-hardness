"""Read-only Full110 package and complete-parent scope gates; no cloud or Lean."""
import json
from pathlib import Path
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full110 import OUTPUT, parent_native_custody
from prepare_complete_operator_scope_v2 import parent, validate, make_successor

HERE = Path(__file__).resolve().parent
RECORD = HERE / 'full110-immutable-capture-record-v1'
INDEX_PIN = '656797281E037B3987680892BD3CAC0BE114572CE2FB5CCBDCB585C6C153087D'
SCOPE_PIN = '892D56612F03C3ED79E1E006B6340B7BC8F3721222CFCA59E5079B8CB2C9B196'


def validate_successor():
    from full109_capture_gates import validate_successor as parent_gate
    parent_gate()
    assert digest(RECORD / 'index.json') == INDEX_PIN, 'Frozen Full110 record drift'
    index = json.loads((RECORD / 'index.json').read_bytes())
    assert digest(HERE / 'prepare_complete_operator_scope_v2.py') == SCOPE_PIN
    package_rows = [row for row in index['files'] if row['copy'].startswith('package/')]
    assert len(package_rows) == 10
    for row in package_rows:
        relative = row['copy'].removeprefix('package/')
        original, saved = OUTPUT / relative, RECORD / row['copy']
        assert original.resolve().is_relative_to(OUTPUT.resolve())
        assert Path(row['original']) == original
        assert original.stat().st_size == row['bytes']
        assert digest(original) == digest(saved) == row['sha256'], 'Frozen package byte drift: ' + relative
    parent_native_custody()
    old, new = parent(), capsule(OUTPUT / 'input-archive.tar.gz')
    assert new == make_successor(old), 'Full110 regenerated input drift'
    validate(old, new)
    assert new['capture-manifest.json'] == (OUTPUT / 'capture-manifest.json').read_bytes()
    manifest = json.loads(new['capture-manifest.json'])
    assert len(manifest['project_sources']) == 369
    assert len(manifest['requested_axioms']) == 347 and len(manifest['stages']) == 7
    print('Full110 frozen full369/full347/seven-stage package scope verified; no launch or native acceptance')


if __name__ == '__main__':
    validate_successor()
