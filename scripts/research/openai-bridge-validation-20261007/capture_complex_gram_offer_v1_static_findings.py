"""Preserve the stable complex Gram offer before the separately routed tactic repair."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PIN = '5828585CBFCC6A6F93688B5E0A0EE306A384E9BE4A2D54DB3A5CD942C8B358ED'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-complex-gram-candidate-v1'
    manifest = (source / 'V1-MANIFEST.json').read_bytes()
    assert sha(manifest) == PIN
    rows = json.loads(manifest)['files'] + [dict(path='V1-MANIFEST.json', bytes=len(manifest), sha256=PIN)]
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    assert sha(contents['ExactComplexRankGram.lean']) == '3B816861F326A014D2D19734142FE0D08E287CADD58774FBBBFA5366E602A336'
    target = HERE / 'complex-gram-offer-capture-v1-static-findings'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.name, files=rows, lexical_preflight=lexical,
                  immutable_capture_acknowledged=True, root_read_complete_source_and_checks=True,
                  root_static_findings=[
                      'Expand the real-left-scalar complex product before rewriting the RHS inner-product component.',
                      'Apply rank-projection component transport to both sides after exposing the RHS inner product.',
                      'Explicitly instantiate n,c,s,i,j in the four standalone real Gram have declarations.'
                  ], launch_admission=False, lean_executed=False, certified=False, accepted=False,
                  successor_must_be_separate=True, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(files=len(rows), exact_stable_source_preserved=True, launch_admission=False)))


if __name__ == '__main__':
    main()
