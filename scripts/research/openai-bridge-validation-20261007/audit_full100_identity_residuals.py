"""Reconcile review residuals against preserved evidence; no Lean or cloud writes."""
import hashlib
import json
from pathlib import Path
import tarfile

from custody_checks import digest, verify_local_custody

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
QUAL = ROOT / 'consumption-v2/qualification'
HERE = Path(__file__).parent


def read(path):
    return json.loads(Path(path).read_bytes())


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    capture = ROOT / 'capture-manifest.json'
    assert digest(capture) == '8E71DE454150DEAC5FE9F12B1DCCF8BA768D7788A70D5F159D436C2682D73D3D'
    manifest = read(capture)
    marker = read(ROOT / 'launch-once.json')
    custody = read(Path(marker['preflight']) / 'terminal-custody.json')['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '66BFF34BC77A2A558BB06EDC6FE9382A2A8210804C56C9499F37218E102E8475'
    with tarfile.open(custody['repository_path']) as archive:
        objects = json.loads(archive.extractfile('object-after.json').read())
        before = json.loads(archive.extractfile('source-before.json').read())
        after = json.loads(archive.extractfile('source-after.json').read())
        patch = archive.extractfile('cslib-tracked-diff.patch').read()
    assert before == after
    expected = sorted('.lake/build/lib/lean/' + p.removeprefix('lean/').removesuffix('.lean') + '.olean'
                      for p in manifest['project_sources'])
    assert len(expected) == 327 and set(expected) <= set(objects)
    oleans = sorted(p for p in objects if p.endswith('.olean'))
    sidecars = sorted(p for p in objects if p.endswith('.olean.hash'))
    assert len(objects) == 661 and len(oleans) == 331 and len(sidecars) == 330
    surplus = sorted(set(oleans) - set(expected))
    unpaired = sorted(p for p in oleans if p + '.hash' not in objects)
    assert len(surplus) == 4 and len(unpaired) == 1
    assert all(p.removesuffix('.hash') in objects for p in sidecars)

    index_path = QUAL / 'review-sources/source-index.json'
    assert digest(index_path) == '86C36CF4937800D55848BEE08415DC8D29B3DF56B349FD53D8AE12331FF0EF18'
    index = read(index_path)
    external = {}
    for boundary in index['external_boundaries']:
        row = boundary['source']
        path = row['packet_path']
        if path in external:
            assert external[path] == row
        external[path] = row
    assert len(external) == 409
    for rel, row in external.items():
        path = QUAL / 'review-sources' / rel
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    cslib = [r for r in external.values() if 'cslib' in r['source_path'].lower() or '/cslib/' in r['packet_path'].lower()]
    assert not cslib
    rel = 'lean/PvNP/RealizableHardness/BinaryMatrixFourier.lean'
    pin = manifest['project_sources'][rel]
    assert pin['sha256'] == '810324DDAD55B909A4EBA239FA3CB6988858A9426DC77ADEBEC051B0C11A70D8'
    assert digest(QUAL / 'review-sources' / rel) == pin['sha256']
    # Native source maps may store a digest string or an explicit metadata row.
    value = after[rel]
    assert (value['sha256'] if isinstance(value, dict) else value) == pin['sha256']
    diagonal = external['external/Mathlib/Data/Matrix/Diagonal.lean']
    reports = {}
    for lens in ['proof-adversarial', 'complexity', 'non-claims']:
        p = HERE / 'full100-identity-addendum-reports' / (lens + '-01.md')
        receipt = read(p.with_suffix('.json'))
        assert digest(p) == receipt['report_sha256'] and receipt['native_exit'] == 0
        reports[lens] = dict(report_sha256=digest(p), receipt_sha256=digest(p.with_suffix('.json')))
    result = dict(schema='full100-identity-residual-root-audit-v1', native_custody=custody,
        capture_sha256=digest(capture), source_index_sha256=digest(index_path), reports=reports,
        Fourier_source_capture_record=pin, Fourier_native_source_after_record=value,
        Fourier_complete_body_matches_capture_and_native_source_after=True,
        expected_captured_olean_paths=expected, all_327_expected_oleans_present=True,
        actual_artifact_count=661, actual_olean_count=331, actual_sidecar_count=330,
        surplus_objects={p: objects[p] for p in surplus}, unpaired_objects={p: objects[p] for p in unpaired},
        surplus_in_frozen_warm_inventory={p: p in manifest['cache_provenance']['objects'] for p in surplus},
        surplus_provenance_and_missing_sidecar_explanation='Unresolved; do not infer inherited warm status or source certification from object presence.',
        complete_external_files_current_hash_verified=409, cslib_files_in_external_source_index=0,
        cslib_patch_bytes=len(patch), cslib_patch_sha256=sha(patch),
        cslib_disposition='Outside the indexed consumed declaration-source closure; nonempty patch remains preserved. No claim of clean whole-package checkout.',
        transpose_one_source=diagonal,
        transpose_one_disposition='Exact source hash reverified; independent complete-body review remains pinned-library trust.',
        original_reports_unchanged=True, terminal_receipt_is_not_coverage_certificate=True,
        compiled_object_binary_archive_claimed=False, fresh_checkout_replay_completed=False,
        universal_Spectral47_native_accepted=False, manuscript_fidelity_closed=False,
        conditional_integration_verdict='GO-WITH-NOTES unchanged', R14='HIGH open', overall_GO=False, full_goal_complete=False)
    output = QUAL / 'identity-residual-root-audit-v1.json'
    data = (json.dumps(result, indent=2) + '\n').encode('utf-8')
    if output.exists():
        assert output.read_bytes() == data
    else:
        with output.open('xb') as stream:
            stream.write(data)
    print(json.dumps(dict(audit_sha256=digest(output), expected=327, oleans=331, sidecars=330,
                         cslib_consumed_files=0, Fourier_identity_closed=True, overall_GO=False)))


if __name__ == '__main__':
    main()
