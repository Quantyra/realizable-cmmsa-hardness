"""Preserve a stable offer rejected by root's complete source review, before repair."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v1 import inspect_bytes

HERE = Path(__file__).resolve().parent
MANIFEST = 'C24F0338B2C48BDF870F193C342021CCC297F601201904696F52C3C81EB8C595'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-complex-append-candidate-v2'
    manifest = (source / 'offer-manifest.json').read_bytes()
    assert sha(manifest) == MANIFEST
    rows = json.loads(manifest)['files']
    rows += [dict(path='offer-manifest.json', bytes=len(manifest), sha256=MANIFEST)]
    contents = {}
    checks = []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            checks.append(inspect_bytes(data, row['path']))
    lines = contents['ExactComplexAppendContinuation.lean'].decode('utf-8').splitlines()
    corrupt = [dict(line=i, text=line) for i, line in enumerate(lines, 1) if '?' in line]
    assert len(corrupt) == 17
    target = HERE / 'complex-offer-capture-v2-static-failure'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.name, files=rows,
                  immutable_capture_acknowledged=True, root_read_complete_offer=True,
                  previous_lexical_preflight=checks,
                  previous_preflight_did_not_detect_ascii_question_mark_glyph_loss=True,
                  actual_question_mark_source_lines=corrupt,
                  launch_admission=False, lean_executed=False, accepted=False,
                  root_static_findings=[
                      'Literal ASCII question marks replaced arrows, quantifiers, logical connectives, product notation, inequalities and tactic bullets in 17 source lines.',
                      'Rank-projection component proofs rewrite coefficient re/im while still inside an unexpanded complex product.',
                      'Pointwise transport inside append/Phi function arguments requires binder-aware simplification.',
                      'Main energy proof requests component rewrites after hRight has already eliminated those occurrences.',
                      'Checks uses only #check; public source declarations need fresh axiom profiles in the eventual harness.'
                  ], successor_must_be_separate=True)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(preserved_files=len(rows), actual_corrupt_lines=len(corrupt), launch_admission=False)))


if __name__ == '__main__':
    main()
