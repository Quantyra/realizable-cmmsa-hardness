"""Capture unchanged argument reports and their explicit metadata correction."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    supplied = [
        ('numeric-explicit-height-argument-v1/ARGUMENT.json', '9460B2B8C692885E940C5C275A234030FC70FF0422C175F1D53F7E5EC2C509AE'),
        ('numeric-source-height-independent-static-review-v1/review.json', '57EAA55FF6E297194A29A04FD983BF35C2CCB419325EB95A389FD0DAAD2184D4'),
        ('numeric-source-height-independent-static-review-v1/review-addendum.json', None)]
    out = HERE / 'numeric-argument-review-capture-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for relative, expected in supplied:
        source = HERE / relative
        before = digest(source)
        assert expected is None or before == expected
        value = json.loads(source.read_bytes())
        if source.name == 'review-addendum.json':
            assert value['parent_review_sha256'] == supplied[1][1]
            assert value['correction']['correct_pinned_source'].endswith('/ActualStarFixedRhoDimensionGuard.lean')
        target = out / source.name
        target.open('xb').write(source.read_bytes())
        assert digest(source) == digest(target) == before
        rows.append(dict(original=relative, copy=target.name, bytes=source.stat().st_size, sha256=before))
    assert digest(HERE / 'numeric-source-height-offer-capture-v3/index.json') == '7CD8C1D6463A39ECDE018F278360847F6874C3F8A2A3CB57FFC2D687B025C96D'
    assert digest(HERE / 'numeric-scalar-offer-capture-v5/index.json') == '3026BCA76A941ED298733F3CCBC2AEDDA3C28BF196B977A7E9D3E0AF93C10701'
    value = dict(schema='numeric-argument-review-capture-v1', files=rows,
        root_read_complete_original_reports=True,
        root_assessment='Explicit nested-max numeric floor suffices conditionally; O(m^13) in the numeric parameter, relative to supplied effective base/cutoff.',
        corrected_metadata_preserved_in_separate_addendum=True,
        T_need_not_be_dyadic_but_material_k_must_be=True,
        open_obligations=['GCP source verification', 'effective satisfying common spectral/source cutoff',
            'same-instance source/table/sampler/lower-signal', 'encoded reduction and runtime/learning',
            'external milestone and final reviews'],
        independent_static_review_is_not_external_provider_acceptance=True,
        compiler_invoked=False, full_goal_complete=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2) + '\n')
    print(json.dumps(dict(folder=str(out), original_reports=len(rows), index_sha256=digest(out / 'index.json'))))


if __name__ == '__main__':
    main()
