"""Preserve repaired complex Gram proof with exact unchanged theorem statements."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PIN = '5C647C53FE8519629EE4906AD642E38AE175ADD3FDE0913722C5827E76690D5F'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-complex-gram-candidate-v2'
    manifest = (source / 'V2-MANIFEST.json').read_bytes()
    assert sha(manifest) == PIN
    rows = json.loads(manifest)['files'] + [dict(path='V2-MANIFEST.json', bytes=len(manifest), sha256=PIN)]
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    old = HERE / 'complex-gram-offer-capture-v1-static-findings'
    assert contents['ExactComplexRankGramChecks.lean'] == (old / 'ExactComplexRankGramChecks.lean').read_bytes()
    before = (old / 'ExactComplexRankGram.lean').read_text(encoding='utf-8')
    after = contents['ExactComplexRankGram.lean'].decode('utf-8').replace('\r\n', '\n')
    start = '  have hFparts := (complexRightInvariant_iff_components F).mp hF'
    end = '/-- The complete append Gram matrix is exactly diagonal by rank. -/'
    assert before.split(start)[0] == after.split(start)[0]
    assert before.split(end)[1] == after.split(end)[1]
    target = HERE / 'complex-gram-offer-capture-v2'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.name, files=rows, lexical_preflight=lexical,
                  immutable_capture_acknowledged=True, root_source_body_and_argument_review=True,
                  theorem_statements_and_checks_unchanged_from_preserved_v1=True,
                  source_changes_limited_to_main_proof_body=True,
                  both_sides_component_transport_after_complex_product_expansion=True,
                  four_real_Gram_instances_explicitly_dimension_and_rank_bound=True,
                  arbitrary_two_function_cross_rank_orthogonality=True,
                  invariant_two_function_append_gram_all_natural_ranks=True,
                  conjugate_first_pairing=True, above_width_zero_and_empty_product_preserved=True,
                  dependencies_uncompiled=True, lean_executed=False, certified=False, accepted=False,
                  whole_hypercontractivity_appendix_not_certified=True, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(files=len(rows), unchanged_statements_and_checks=True, native_verified=False)))


if __name__ == '__main__':
    main()
