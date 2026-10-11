"""Preserve exact stable real offer and the terminally interrupted complex draft."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v1 import inspect_bytes

HERE = Path(__file__).resolve().parent
MANIFEST_PIN = 'DD8BD5394958C050BD85BCDD0319A4EF6ADECA9E0E26F66B73FCAB52FFE1D1C2'
COMPLEX_PIN = '4A24D8574ED5EBA0A041C9868C96C98FA323DB02997F9D14821812215BC67FD5'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-operator-continuation-candidate-v3'
    manifest = (source / 'V3-MANIFEST.json').read_bytes()
    assert sha(manifest) == MANIFEST_PIN
    rows = json.loads(manifest)['files']
    assert len(rows) == 18
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows} | {'V3-MANIFEST.json'}
    rows = rows + [dict(path='V3-MANIFEST.json', bytes=len(manifest), sha256=MANIFEST_PIN)]
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert sha(data) == row['sha256'].upper() and len(data) == row['bytes']
        text = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
        contents[row['path']] = data
    assert len(lexical) == 11
    interrupted = HERE / 'exact-complex-append-candidate-v1/ExactComplexAppendContinuation.lean'
    partial = interrupted.read_bytes()
    assert sha(partial) == COMPLEX_PIN and len(partial) == 12041
    partial.decode('utf-8')
    assert not partial.startswith(b'\xef\xbb\xbf')
    target = HERE / 'operator-complete-offer-capture-v3'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.relative_to(HERE).as_posix(), files=rows,
                  lexical_preflight=lexical, author_offer_frozen=True,
                  immutable_capture_acknowledged=True, root_source_body_review=True,
                  gPhi_target_preserves_unrestricted_B_and_arbitrary_M=True,
                  adjoint_invariant_first_argument_only=True,
                  root_static_repairs_before_freeze=['Explicit Phi s parameter',
                      'Correct adjoint reindex equality directions and raw frame input type',
                      'Pinned Finset.sum_comm API and balanced delimiters',
                      'Corrected historical block dimensions and superseded-gap annotation'],
                  lean_executed=False, certified=False, accepted=False,
                  dependency_capture_complete=False, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    failed = HERE / 'complex-interrupted-author-capture-v1'
    failed.mkdir(exist_ok=False)
    (failed / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (failed / interrupted.name).open('xb').write(partial)
    failure = dict(original=interrupted.relative_to(HERE).as_posix(), bytes=len(partial),
                   sha256=COMPLEX_PIN, author_stable_offer_received=False,
                   provider_turns_terminal_failed=True, root_read_complete_draft=True,
                   request_ids=['a981eeae-1810-406f-8aa9-129b1c1975f1',
                                '7d5a7650-da3d-45ae-a444-0b662cb093f3'],
                   reported_error='stream disconnected before completion; request processing error',
                   complete_provider_raw_transport_not_available=True,
                   source_preserved_before_any_successor_edit=True,
                   lean_executed=False, certified=False, accepted=False,
                   root_static_findings=[
                       'Import the pinned Complex.BigOperators source for re_sum/im_sum explicitly.',
                       'Expand complex product re/im before rewriting coefficient component lemmas.',
                       'Energy proof contains malformed application parentheses and redundant post-hRight rewrites.',
                       'Use pointwise simplification under function binders for real/imag transports.',
                       'Checks and argument map were not produced before the author failure.'])
    (failed / 'index.json').write_text(json.dumps(failure, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(real_files=len(rows), real_lean_files=len(lexical),
                          interrupted_complex_source_preserved=True, accepted=False)))


if __name__ == '__main__':
    main()
