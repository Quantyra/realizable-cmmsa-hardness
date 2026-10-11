"""Capture coherent literal complex append, G/Phi and restricted-adjoint offer."""
import hashlib
import json
from pathlib import Path
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
PIN = '39ACBE7B538EC5352D1C8BF46054BB7DD5BDD5F5B87EE157B7B20B5ACFB62542'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = HERE / 'exact-complex-append-candidate-v4'
    manifest = (source / 'offer-manifest.json').read_bytes()
    assert sha(manifest) == PIN
    rows = json.loads(manifest)['files'] + [dict(path='offer-manifest.json', bytes=len(manifest), sha256=PIN)]
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows}
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    target = HERE / 'complex-operator-complete-offer-capture-v4'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
    record = dict(original_directory=source.name, files=rows, lexical_preflight=lexical,
                  immutable_capture_acknowledged=True, root_source_body_and_argument_review=True,
                  continuation_diff_from_preserved_v3_limited_to_scalar_simplifications=True,
                  exact_normSq_energy_without_factor_two_loss=True,
                  literal_complex_G_T_Phi_definitions=True, paired_inverse_full_carrier_invariance=True,
                  conjugate_first_inner_product=True, restricted_adjoint_K_only_invariant_H_arbitrary=True,
                  generic_totalized_empty_mean_retained=True,
                  real_operator_and_eigenrelation_dependencies_uncompiled=True,
                  complex_two_function_gram_not_in_this_offer=True,
                  whole_complex_hypercontractivity_appendix_not_certified=True,
                  lean_executed=False, certified=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(offer_files=len(rows), lean_files=len(lexical),
                          static_source_review_complete=True, native_verified=False)))


if __name__ == '__main__':
    main()
