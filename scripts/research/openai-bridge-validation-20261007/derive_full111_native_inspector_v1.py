"""Bind the preserved read-only observer to the original Full111 launched run."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full111_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'inspect_full110_native_progress_v2.py'
    assert digest(source) == '64063C93861C2176E353792F3BF76337E0C8C53F5F5E7D62CFB9E74E6010E2B2'
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    run = marker['run']
    assert run.startswith('cmmsa_a8_output_20261011T')
    assert json.loads((ROOT / 'resource-binding.json').read_bytes())['vm_id'] == VM_ID
    manifest = json.loads((ROOT / 'capture-manifest.json').read_bytes())
    assert [row['index'] for row in manifest['stages']] == list(range(7))
    replacements = [
        ('full110', 'full111'),
        ('full111-exact-real-complex-operators-resource02', ROOT.name),
        ('cmmsa_a8_output_20261011T025221Z_7046a7c0', run),
        ('live-native-inspections-v2', 'live-native-inspections-v1')]
    after = source.read_text(encoding='utf-8')
    recorded = []
    for old, new in replacements:
        count = after.count(old)
        assert count > 0
        recorded.append(dict(before=old, after=new, count=count))
        after = after.replace(old, new)
    ast.parse(after)
    assert 'range(7)' in after
    target = HERE / 'inspect_full111_native_progress_v1.py'
    target.open('xb').write(after.encode('utf-8'))
    value = dict(source=str(source), source_sha256=digest(source), target=str(target),
        target_sha256=digest(target), exact_replacements=recorded, run=run,
        launch_marker_sha256=digest(ROOT / 'launch-once.json'), stages=list(range(7)),
        read_only=True, original_compiler_replayed=False, unchanged_transport_and_host_key_guards=True)
    (HERE / 'full111-native-inspector-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(value), flush=True)


if __name__ == '__main__':
    main()
