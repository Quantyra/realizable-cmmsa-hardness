"""Capture the glyph-correct successor and retain remaining static tactic findings."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PIN = 'AD57B2429D71EC94EF8A6FD932C7544F66E25378FC50494B3BEE50A6B550497A'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-complex-append-candidate-v3'
    manifest = (source / 'offer-manifest.json').read_bytes()
    assert sha(manifest) == PIN
    rows = json.loads(manifest)['files'] + [dict(path='offer-manifest.json', bytes=len(manifest), sha256=PIN)]
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows}
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    target = HERE / 'complex-offer-capture-v3'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.name, files=rows, lexical_preflight=lexical,
                  immutable_capture_acknowledged=True, root_read_complete_offer=True,
                  known_glyph_loss_repaired=True, previous_component_rewrite_findings_repaired=True,
                  remaining_static_findings=[
                      'In complexPhi_rankProjection_eigen, real scalar is the left factor. Its zero imaginary part creates zero_mul, not mul_zero.',
                      'Imaginary scalar-product branch also requires add_zero, not only zero_add, after removing its zero second summand.',
                      'Use both zero_mul/mul_zero and add_zero/zero_add or the appropriate exact rules in a separately preserved successor.'
                  ], lean_executed=False, launch_admission=False, certified=False, accepted=False,
                  fresh_native_profiles_and_independent_review_required=True, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(files=len(rows), lexical_preflight_passed=True, launch_admission=False)))


if __name__ == '__main__':
    main()
