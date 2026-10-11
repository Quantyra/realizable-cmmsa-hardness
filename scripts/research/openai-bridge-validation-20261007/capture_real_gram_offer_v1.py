"""Preserve the exact two-function real Gram offer and the misplaced initial draft."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PIN = '43A810D62810B30683681A0B32A8CCAE2C30F14B37F3FBFB70D848D15316CE7D'
DRAFT_PIN = '3A63A7ACA81873EF66C05ECF6EA7CE4D95B84481BDEC071D80D1F7531F05A812'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-real-gram-candidate-v1'
    manifest = (source / 'V1-MANIFEST.json').read_bytes()
    assert sha(manifest) == PIN
    rows = json.loads(manifest)['files'] + [dict(path='V1-MANIFEST.json', bytes=len(manifest), sha256=PIN)]
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows}
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    original_draft = HERE / 'B/exact-real-gram-candidate-v1/ExactRealRankGram.lean'
    draft = original_draft.read_bytes()
    assert sha(draft) == DRAFT_PIN
    target = HERE / 'real-gram-offer-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    (target / 'misplaced-initial-draft.lean').open('xb').write(draft)
    record = dict(original_directory=source.name, files=rows, lexical_preflight=lexical,
                  misplaced_initial_draft=dict(original=original_draft.relative_to(HERE).as_posix(),
                      copy='misplaced-initial-draft.lean', bytes=len(draft), sha256=DRAFT_PIN,
                      historical_draft_only=True, not_part_of_candidate_compile_scope=True),
                  immutable_capture_acknowledged=True, root_read_complete_offer=True,
                  existing_qualified_projection_invariance_reused=True,
                  direct_two_function_parseval=True, both_inputs_invariant_in_operator_gram=True,
                  no_rank_upper_bound_required=True, exact_above_width_zero_projection_included=True,
                  prefreeze_repairs=['Full d/s/j eigenvalue arity', 'Finite-sum binder transport',
                      'Explicit equal-rank filter expansion', 'Scalar normalization',
                      'Fully qualified fresh axiom requests'],
                  real_operator_dependencies_uncompiled=True, lean_executed=False,
                  certified=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(offer_files=len(rows), lean_files=len(lexical),
                          historical_draft_preserved=True, native_verified=False)))


if __name__ == '__main__':
    main()
