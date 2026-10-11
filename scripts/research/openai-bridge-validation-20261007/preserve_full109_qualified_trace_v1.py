"""Preserve complete qualified trace/source/packet bytes and original stop/qualification terminals."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest
from full109_consumption_v3_controller import ROOT

HERE = Path(__file__).resolve().parent
WRAPPERS = {
    'terminate_full109_consumption_v3.py': '20261011T022727967023Z-a8d39902d5c0',
    'qualify_full109_consumption_v3.py': '20261011T023158300547Z-aa87055f1bbd',
    'prepare_full109_consumption_review_sources.py': '20261011T023256217692Z-1f6a6c2b5be2',
    'audit_full109_prior_review_reuse_v1.py': '20261011T023409381634Z-6855818233ed',
    'prepare_full109_material_integration_v1.py': '20261011T023552653035Z-47c4171600b3',
}


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    base = ROOT / 'qualification'
    summary = read(base / 'qualification-summary.json')
    assert summary['structural_trace_qualification'] and not any(summary['unresolved_by_graph'].values())
    assert summary['nodes'] == 8299 and len(summary['project_modules']) == 218
    reuse = read(base / 'prior-review-reuse-audit.json')
    assert reuse['all346_per_lens_prior_body_coverage_identity_eligible'] and len(reuse['reports']) == 45
    manifest = read(base / 'material-integration-v1/manifest.json')
    assert manifest['complete_file_union_preserved'] == 100 and len(manifest['packets']) == 2
    marker = read(ROOT / 'launch-once.json')
    check = Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT / 'checks').resolve(strict=True))
    stop = read(check / 'vm-termination.json')
    assert str(stop['independent']['id']) == '7237681467779354904'
    assert stop['independent']['status'] == 'TERMINATED' and stop['custody_verified_before_stop']
    paths = {check / 'vm-termination.json', Path(__file__).resolve()}
    paths.update(p for p in (check / 'termination-controls').rglob('*') if p.is_file())
    for action, name in WRAPPERS.items():
        folder = ROOT.parent / 'research-resume-20261010' / name
        command = read(folder / 'command.json')
        assert command['native_exit'] == 0 and any(str(x).endswith(action) for x in command['argv'])
        assert digest(folder / action) == command['source_sha256']
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == command[stream + '_sha256']
        paths.update(p for p in folder.iterdir() if p.is_file())
    members = {p for p in base.iterdir() if p.is_file()}
    for name in ('graphs', 'tooling', 'review-sources'):
        members.update(p for p in (base / name).rglob('*') if p.is_file())
    # Review children are live and intentionally not part of this settled qualification record.
    members.update(p for p in (base / 'material-integration-v1').iterdir() if p.is_file())
    pins = {p.relative_to(base).as_posix(): dict(original=str(p), bytes=p.stat().st_size, sha256=digest(p))
            for p in sorted(members)}
    archive_folder = ROOT / 'qualified-custody-v1'
    archive_folder.mkdir(exist_ok=False)
    archive_path = archive_folder / 'complete-qualified-trace-sources-packets.tar.gz'
    with archive_path.open('xb') as stream:
        with tarfile.open(fileobj=stream, mode='w:gz', compresslevel=6) as archive:
            for name, row in pins.items():
                archive.add(row['original'], arcname=name, recursive=False)
    with tarfile.open(archive_path, 'r:gz') as archive:
        actual = set()
        for member in archive:
            assert member.isfile() and member.name in pins and member.name not in actual
            actual.add(member.name)
            row = pins[member.name]
            assert member.size == row['bytes']
            state = hashlib.sha256()
            stream = archive.extractfile(member)
            while data := stream.read(1024 * 1024):
                state.update(data)
            assert state.hexdigest().upper() == row['sha256'] == digest(row['original'])
        assert actual == set(pins)
    archive_index = archive_folder / 'archive-index.json'
    archive_index.open('x', encoding='utf-8').write(json.dumps(dict(
        archive_sha256=digest(archive_path), archive_bytes=archive_path.stat().st_size,
        members=pins, every_member_verified_against_original=True,
        no_original_files_deleted=True, live_review_outputs_excluded=True), indent=2)+'\n')
    paths.update((archive_path, archive_index))
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full109-resume-qualified-trace-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name,
                         bytes=original.stat().st_size, sha256=digest(original)))
    index = dict(schema='full109-qualified-trace-complete-custody-v1', files=rows,
                 graph_nodes=8299, project_modules=218, external_boundaries=2767,
                 required_roots=261, focused_roots=93, unresolved=0,
                 unchanged_prior_bodies=346, prior_reports_verified=45,
                 complete_capture_bodies=348, complete_review_file_union=100,
                 qualified_archive_members=len(pins), qualified_archive_sha256=digest(archive_path),
                 original_terminal_handles=dict(stop=92177, qualification=60885, sources=26504, reuse=24045),
                 independent_vm_termination_proven=True, structural_qualification_complete=True,
                 semantic_review_complete=False, accepted=False, full_goal_complete=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(index, indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), original_files=len(rows), archive_members=len(pins),
                         archive_bytes=archive_path.stat().st_size, archive_sha256=digest(archive_path),
                         structural_qualification_complete=True, accepted=False)), flush=True)


if __name__ == '__main__':
    main()
