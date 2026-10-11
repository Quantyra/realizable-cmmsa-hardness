"""Capture root's uncompiled source-height candidate and exact dependency pins."""
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
ARCHIVE = Path('C:/Users/dfred/.quantyra/builder02/full110-exact-real-complex-operators-resource02/input-archive.tar.gz')


def main():
    assert digest(ARCHIVE) == 'C1702903ECC5F939B9504371D63F0D4313E192446971EF0DD7627F6E770F3C61'
    source = HERE / 'actual-numeric-source-height-candidate-v2'
    names = ['ActualNumericSourceHeight.lean', 'ActualNumericSourceHeightChecks.lean', 'ARGUMENT-MAP.md']
    rows, lexical = [], []
    for name in names:
        data = (source / name).read_bytes()
        assert not data.startswith(b'\xef\xbb\xbf')
        data.decode('utf-8')
        rows.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
        if name.endswith('.lean'):
            lexical.append(inspect_bytes(data, name))
    dependencies = []
    with tarfile.open(ARCHIVE, 'r:gz') as archive:
        for name in ['ActualSelectedSpectralParameters.lean', 'SamplerParameters.lean',
                     'ActualStarFixedRhoDimensionGuard.lean', 'ActualCmmsaParameterReconciliation.lean',
                     'ActualCmmsaAdmissibilitySelector.lean']:
            members = [m for m in archive.getmembers() if m.name.endswith('/' + name)]
            assert len(members) == 1 and members[0].isfile()
            data = archive.extractfile(members[0]).read()
            dependencies.append(dict(member=members[0].name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    assert dependencies[0]['sha256'] == '78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582'
    interrupted = HERE / 'actual-numeric-source-height-candidate-v1'
    observed = sorted(str(p) for p in interrupted.rglob('*') if p.is_file()) if interrupted.exists() else []
    assert not observed
    value = dict(offer=source.name, author='root', status='stable uncompiled source-height candidate',
        files=rows, dependencies=dependencies, dependency_archive=dict(path=str(ARCHIVE), sha256=digest(ARCHIVE)),
        lexical_preflight=lexical, lean_executed=False, native_verified=False, accepted=False,
        full_goal_complete=False, provider_interruption_observation=dict(
            request_id='c24e3749-384c-4c23-bb06-44db154a019a', assigned_v1_path=str(interrupted),
            observed_files=observed, root_observation_not_raw_transcript=True),
        remaining=['Selector inhabitance at the enlarged base', 'Effective common scalar cutoff',
                   'Same-instance source/table/sampler and lower signal', 'GCP kernel/axiom/trace and review'])
    manifest = source / 'OFFER-MANIFEST.json'
    manifest.open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    rows = [*rows, dict(path=manifest.name, bytes=manifest.stat().st_size, sha256=digest(manifest))]
    target = HERE / 'numeric-source-height-offer-capture-v2'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for row in rows:
        data = (source / row['path']).read_bytes()
        (target / row['path']).open('xb').write(data)
        assert len(data) == row['bytes'] and digest(target / row['path']) == row['sha256']
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    index = dict(original_directory=str(source), files=rows, dependencies=dependencies,
        dependency_archive_sha256=digest(ARCHIVE), lexical_preflight=lexical, immutable_capture=True,
        source_review_complete=True, no_old_selector_witness_reused=True,
        selected_instance_existence_proved=False, compiler_invoked=False, native_verified=False, accepted=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(index, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), source=rows[0], index_sha256=digest(target / 'index.json'),
        compiler_invoked=False, native_verified=False)), flush=True)


if __name__ == '__main__':
    main()
