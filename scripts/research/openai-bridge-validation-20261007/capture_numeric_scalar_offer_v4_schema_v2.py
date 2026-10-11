"""Freeze the scalar v4 successor and its remaining static review findings."""
import difflib
import hashlib
import json
from pathlib import Path
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def main():
    prior = HERE / 'numeric-scalar-offer-capture-v3'
    assert digest(prior / 'index.json') == 'F3B0F6BBC5F65A2E64A2C0C24A045C1E414750F9F22C0D4882FE101AED4C915F'
    old = json.loads((prior / 'index.json').read_bytes())
    for row in old['files']:
        assert digest(prior / row['path']) == row['sha256']
    source = HERE / 'actual-numeric-no-scalar-candidate-v4'
    assert digest(source / 'ActualNumericNoScalar.lean') == 'D3AF980C7BABBD03EB23AB0B55D419D2D0FAB5EAFAC15E3A95C3473C5E4816AE'
    offered = json.loads((source / 'OFFER-MANIFEST.json').read_bytes())
    assert offered['dependencies'] == old['dependencies']
    pins = {row['path']: row for row in offered['files']}
    assert len(pins) == len(offered['files'])
    assert offered['dependency_archive']['sha256'] == old['dependency_archive_sha256']
    assert digest(Path(old['dependency_archive'])) == old['dependency_archive_sha256']
    rows, contents, lexical = [], {}, []
    for path in sorted(source.iterdir()):
        assert path.is_file()
        data = path.read_bytes()
        assert not data.startswith(b'\xef\xbb\xbf')
        data.decode('utf-8')
        sha = hashlib.sha256(data).hexdigest().upper()
        if path.name != 'OFFER-MANIFEST.json':
            pin = pins[path.name]
            assert len(data) == pin['bytes'] and sha == pin['sha256'].upper()
        if path.suffix == '.lean':
            lexical.append(inspect_bytes(data, path.name))
        contents[path.name] = data
        rows.append(dict(path=path.name, bytes=len(data), sha256=sha))
    assert set(contents) == set(pins) | {'OFFER-MANIFEST.json'}
    target = HERE / 'numeric-scalar-offer-capture-v4'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == (source / name).read_bytes()
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    findings = [
        dict(location='hratio/htotal', finding='The first calc step substitutes the bare selectedLowHC46NormBound, but hLowLower bounds the full outer low contribution 2*(2^m*(beta^...*low^m)). Keep that full expression as the intermediate; the next step must use hlow on exactly that expression.'),
        dict(location='hcancel', finding='mul_le_mul_iff_right followed by the less-or-equal glyph is a malformed identifier. Check the actual pinned lemma spelling and type; use the positive-factor cancellation lemma.'),
        dict(location='hproductEq', finding='rw [hE0pow] has no occurrence in the already expanded product. The favorable correction is now mathematically present, but this and the remaining rpow API, associativity and coercion steps still need actual translation repair.'),
        dict(location='hLowPow/hlow/hMiddle', finding='Several proofs still expect ring/nlinarith to supply exponent addition or power identities. Establish explicit pow_add/rpow_add/rpow_mul and cast identities before ring or polynomial inequalities. Check hfactor and hcoeff particularly.'),
    ]
    value = dict(original_directory=str(source), files=rows, lexical_preflight=lexical,
        prior_capture_index_sha256=digest(prior / 'index.json'), dependency_archive_sha256=old['dependency_archive_sha256'],
        dependencies=old['dependencies'], complete_source_checks_and_argument_map_read=True,
        complete_source_diff=''.join(difflib.unified_diff((prior / 'ActualNumericNoScalar.lean').read_text(encoding='utf-8').splitlines(True),
            contents['ActualNumericNoScalar.lean'].decode('utf-8').splitlines(True), fromfile='v3', tofile='v4')),
        beta_and_absorption_argument_repaired=True, favorable_final_exponent_correction_retained=True,
        root_findings=findings, root_static_preflight_passed=False, immutable_capture=True,
        successor_required=True, compiler_input_admitted=False, lean_executed=False, native_verified=False,
        accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), index_sha256=digest(target / 'index.json'), exact_files=len(rows),
        remaining_static_findings=len(findings), lean_executed=False)), flush=True)


if __name__ == '__main__':
    main()
