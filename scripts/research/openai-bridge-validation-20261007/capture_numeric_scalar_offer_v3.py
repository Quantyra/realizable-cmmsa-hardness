"""Preserve a stable scalar offer and root rejection without invoking Lean."""
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'actual-numeric-no-scalar-candidate-v3'
ARCHIVE = Path('C:/Users/dfred/.quantyra/builder02/full110-exact-real-complex-operators-resource02/input-archive.tar.gz')
FINDINGS = [
    ('hBetaLower', 'The attempted eps >= 1/4*4 is not implied. Combine eps >= S with its full exponent: S*2^(-c-ms) = 2^(-2*(m+1)*h+(1998*m+2)*rho*h), then use the positive correction. The current hExponent direction is reversed and rw [he0] has no occurrence.'),
    ('hbetaPos', 'The positivity proof precedes heps0. Prove epsilon positivity first from heps and powTwo_pos.'),
    ('hHC', 'r <= d is not a theorem premise and does not follow from the given local Nat inequalities. The finite-index envelope does not mathematically require r <= d; remove the unnecessary premise rather than inventing a bound.'),
    ('hfrac', 'T is Real, so (T : Nat) is invalid. Cross multiply the positive Real denominators and use hPscale directly.'),
    ('hLowPow', 'An upper bound does not prove nonnegativity of the low sum. Unfold the actual nonnegative sum. Chain pow_le_pow_left through hconst and hEtaPow; current rw [hconst] does not consume hpow.'),
    ('hHigh', 'The displayed hfactor equality double-counts r. Correct exponent is 1-20*m*h+r+(4/3)*r*rho*h. hBpow is an inequality and cannot be used as a rewrite equality. Nat.cast_sub needs 1 <= s, derived from hbr.'),
    ('hAbsorb', 'Exponent comparison -20/3*m*h <= -5-A-C*h is false since A+C*h = 20/3*m*h. Derive 32*D <= 2^(C*h), multiply by 2^(-20/3*m*h), and divide by 32. Current log_rpow rewrite targets a goal without a logarithm; rw [he0] has no occurrence.'),
    ('hratio', 'powTwo_neg is referenced but never declared. Derive the ratio with explicit positive division, rpow subtraction and inverse identities; nlinarith cannot supply those transcendental identities.'),
    ('hBetaUpper', 'Use monotonicity in the base with a nonpositive exponent; rpow_le_rpow_of_exponent_ge controls exponents at a fixed base and cannot consume hbase.'),
    ('hproductEq', 'The displayed exact equality is false: the left exponent equals the right exponent minus 4000*rho^2*h/T. Preserve that correction in an equality, then bound it above by zero for the final inequality.'),
    ('glyphs', 'Three occurrences of 0 left-arrow (2 : Real) and one (2 : Real) left-arrow 0 are invalid proposition glyphs, despite lexical preflight passing. Inspect all mathematical glyphs; lexical checks are not parsing.'),
    ('source bridge', 'Check the exact actualWeightedHighEnergy definition and real/natural s-1 cast before rewriting; hsCast is used before unfolding the RHS that contains it.'),
]


def main():
    manifest = json.loads((SOURCE / 'OFFER-MANIFEST.json').read_bytes())
    assert digest(SOURCE / 'ActualNumericNoScalar.lean') == 'D7CBB25CD4095BA47FCC2C5461C22779D7FBBA5432D3EFAD9EADE095A7D5EA88'
    assert digest(ARCHIVE) == manifest['pinned_dependencies']['Full110_input_archive_sha256']
    dependencies = []
    with tarfile.open(ARCHIVE, 'r:gz') as archive:
        for name, sha in manifest['pinned_dependencies'].items():
            if not name.endswith('.lean'):
                continue
            matches = [m for m in archive.getmembers() if m.name.endswith('/' + name)]
            assert len(matches) == 1 and matches[0].isfile()
            data = archive.extractfile(matches[0]).read()
            assert hashlib.sha256(data).hexdigest().upper() == sha
            dependencies.append(dict(member=matches[0].name, bytes=len(data), sha256=sha))
    for name, key in [('ActualNumericNo.lean', 'numeric_v2_source_sha256'), ('ActualNumericNoChecks.lean', 'numeric_v2_checks_sha256')]:
        assert digest(HERE / 'numeric-no-offer-capture-v2' / name) == manifest['preserved_inputs'][key]
    rows, contents, lexical = [], {}, []
    for path in sorted(SOURCE.iterdir()):
        assert path.is_file()
        data = path.read_bytes()
        assert not data.startswith(b'\xef\xbb\xbf')
        data.decode('utf-8')
        sha = hashlib.sha256(data).hexdigest().upper()
        if path.name != 'OFFER-MANIFEST.json':
            offered = manifest['files'][path.name]
            assert len(data) == offered['bytes'] and sha == offered['sha256'].upper()
        if path.suffix == '.lean':
            lexical.append(inspect_bytes(data, path.name))
        rows.append(dict(path=path.name, bytes=len(data), sha256=sha))
        contents[path.name] = data
    assert set(contents) == set(manifest['files']) | {'OFFER-MANIFEST.json'}
    target = HERE / 'numeric-scalar-offer-capture-v3'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == (SOURCE / name).read_bytes()
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    value = dict(original_directory=str(SOURCE), files=rows, dependencies=dependencies,
        dependency_archive=str(ARCHIVE), dependency_archive_sha256=digest(ARCHIVE),
        lexical_preflight=lexical, complete_source_checks_and_argument_map_read=True,
        root_findings=[dict(location=a, finding=b) for a, b in FINDINGS],
        root_mathematical_and_glyph_preflight_passed=False, immutable_capture=True,
        successor_required=True, compiler_input_admitted=False, lean_executed=False,
        native_verified=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), index_sha256=digest(target / 'index.json'),
        exact_files=len(rows), root_rejected=True, lean_executed=False)), flush=True)


if __name__ == '__main__':
    main()
