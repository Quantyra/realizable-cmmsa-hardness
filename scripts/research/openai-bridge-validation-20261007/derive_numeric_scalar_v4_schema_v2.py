"""Preserve the capture schema failure and adapt to the offered list schema."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'capture_numeric_scalar_offer_v4.py'
    assert not (HERE / 'numeric-scalar-offer-capture-v4').exists()
    replacements = [
        ("    prior_offer = json.loads((prior / 'OFFER-MANIFEST.json').read_bytes())\n    assert offered['pinned_dependencies'] == prior_offer['pinned_dependencies']",
         "    assert offered['dependencies'] == old['dependencies']\n    pins = {row['path']: row for row in offered['files']}\n    assert len(pins) == len(offered['files'])\n    assert offered['dependency_archive']['sha256'] == old['dependency_archive_sha256']"),
        ("pin = offered['files'][path.name]", "pin = pins[path.name]"),
        ("set(offered['files']) |", "set(pins) |")]
    text = source.read_text(encoding='utf-8')
    for before, after in replacements:
        assert text.count(before) == 1
        text = text.replace(before, after)
    ast.parse(text)
    target = HERE / 'capture_numeric_scalar_offer_v4_schema_v2.py'
    target.open('xb').write(text.encode('utf-8'))
    record = dict(original=str(source), original_sha256=digest(source), original_native_exit=1,
        original_error="KeyError: 'pinned_dependencies'", failure_before_capture_creation=True,
        direct_tool_output_not_archived=True, root_observation_not_raw_transcript=True,
        target=str(target), target_sha256=digest(target), exact_replacements=replacements,
        author_offer_unchanged=True, compiler_invoked=False)
    (HERE / 'numeric-scalar-v4-capture-schema-repair-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(original_exit=1, successor=str(target), offered_source_unchanged=True)), flush=True)


if __name__ == '__main__':
    main()
