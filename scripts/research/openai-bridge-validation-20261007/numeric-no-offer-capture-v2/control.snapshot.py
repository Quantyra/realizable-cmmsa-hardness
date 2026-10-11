"""Verify the exact static repairs and freeze the uncompiled numeric-NO successor."""
import difflib
import hashlib
import json
from pathlib import Path
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def main():
    prior = HERE / 'numeric-no-offer-capture-v1'
    assert digest(prior / 'index.json') == '766266B66956E6ABA348B4A733B0DAB9B533B35D68AD2C8DBEADB8978E04C65D'
    old_index = json.loads((prior / 'index.json').read_bytes())
    for row in old_index['files']:
        assert digest(prior / row['path']) == row['sha256'].upper()
        assert (prior / row['path']).read_bytes() == (Path(old_index['original_directory']) / row['path']).read_bytes()
    source = HERE / 'actual-numeric-no-candidate-v2'
    manifest = source / 'OFFER-MANIFEST.json'
    assert digest(manifest) == '547D2E531F8D9A9E5EA2E47DE919B0A656F55E26563479324B59D2D8037C93DE'
    rows = json.loads(manifest.read_bytes())['files']
    rows.append(dict(path=manifest.name, bytes=manifest.stat().st_size, sha256=digest(manifest)))
    assert {p.name for p in source.iterdir() if p.is_file()} == {r['path'] for r in rows}
    contents, lexical = {}, []
    for row in rows:
        data = (source / row['path']).read_bytes()
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256'].upper()
        assert not data.startswith(b'\xef\xbb\xbf') and '?' not in data.decode('utf-8')
        contents[row['path']] = data
        if row['path'].endswith('.lean'):
            lexical.append(inspect_bytes(data, row['path']))
    old = (prior / 'ActualNumericNo.lean').read_text(encoding='utf-8')
    replacements = [
        ('ActualNumericNoCandidate', 'ActualNumericNo', 2),
        ('{V : Type*} [Fintype V]', '{V : Type*} [AddCommGroup V] [Module F V] [Fintype V]', 5),
        ('∀ _W : BinaryMatrix n d, (1 : Real)', '∑ _W : BinaryMatrix n d, (1 : Real)', 1),
        ('private theorem booleanRankEnergy_total_le_one', 'theorem booleanRankEnergy_total_le_one', 1)]
    expected = old
    for before, after, count in replacements:
        assert expected.count(before) == count
        expected = expected.replace(before, after)
    assert expected.encode('utf-8') == contents['ActualNumericNo.lean']
    assert contents['ActualNumericNoChecks.lean'] == (prior / 'ActualNumericNoChecks.lean').read_bytes()
    target = HERE / 'numeric-no-offer-capture-v2'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for name, data in contents.items():
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == (source / name).read_bytes()
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    value = dict(original_directory=str(source), files=rows, lexical_preflight=lexical,
        prior_capture_index_sha256=digest(prior / 'index.json'), exact_source_replacements=replacements,
        complete_source_diff=''.join(difflib.unified_diff(old.splitlines(True), expected.splitlines(True), fromfile='v1', tofile='v2')),
        source_namespace_and_nine_requests_aligned=True, prior_static_findings_repaired=True,
        complete_argument_map_read=True, prose_lost_glyphs_repaired=True,
        dependency_pins=old_index['dependencies'], dependency_archive_sha256=old_index['dependency_archive_sha256'],
        root_read_complete_offer_by_full_v1_body_and_exact_v2_diff=True,
        immutable_capture_acknowledged=True, lean_executed=False, native_verified=False,
        accepted=False, full_goal_complete=False,
        remaining=['GCP translation diagnostics and exact native/axiom/trace/body review',
                   'Same-instance explicit source floor, selector/sampler and lower signal',
                   'Complete conservative scalar comparison and numeric NO'])
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), files=len(rows), exact_static_repairs_verified=True,
                         index_sha256=digest(target / 'index.json'), native_verified=False)))


if __name__ == '__main__':
    main()
