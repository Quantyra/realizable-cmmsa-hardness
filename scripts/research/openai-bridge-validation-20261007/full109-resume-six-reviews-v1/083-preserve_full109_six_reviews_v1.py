"""Copy every original review input, terminal stream, receipt and root settlement."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from audit_full109_prior_review_reuse_v1 import BASE, HERE, ROOT, LENSES


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    reports = HERE / 'full109-material-integration-reports-v1'
    settlement = read(reports / 'root-reconciliation-v1.json')
    assert settlement['reports_read_in_full'] and settlement['conditional_crosslevel_milestone_accepted']
    assert not settlement['overall_accepted'] and len(settlement['reports']) == 6
    attributes = '* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n'
    (reports / '.gitattributes').open('x', encoding='utf-8').write(attributes)
    paths = {p for p in reports.iterdir() if p.is_file()}
    paths.add(BASE / 'material-integration-v1/manifest.json')
    paths.update(HERE / name for name in ('run_full109_material_integration_v1.py',
        'run_full90_material_review_packet.py', 'preserve_full109_material_integration_v1.py',
        'preserve_full90_material_review_terminal.py', 'reconcile_full109_material_integration_v1.py',
        'preserve_full109_six_reviews_v1.py'))
    wrappers = []
    for lens in LENSES:
        for number in (1, 2):
            receipt = read(reports / f'{lens}-{number:02d}.json')
            folder = Path(receipt['raw_stdout_path']).parent
            assert digest(folder / 'stdout.json') == receipt['raw_stdout_sha256']
            assert digest(folder / 'stderr.txt') == receipt['raw_stderr_sha256']
            assert int((folder / 'native-exit.txt').read_text()) == 0
            paths.update(p for p in folder.iterdir() if p.is_file())
            found = []
            for command_path in (ROOT.parent / 'research-resume-20261010').glob('*/command.json'):
                command = read(command_path)
                if command['argv'][-2:] == [lens, str(number)] and any(str(x).endswith('run_full109_material_integration_v1.py') for x in command['argv']):
                    assert command['native_exit'] == 0
                    for stream in ('stdout', 'stderr'):
                        assert digest(command_path.parent / stream) == command[stream + '_sha256']
                    found.append(command_path.parent)
            assert len(found) == 1
            wrappers.append(str(found[0]))
            paths.update(p for p in found[0].iterdir() if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    target = HERE / 'full109-resume-six-reviews-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text(attributes, encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = target / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(original) == digest(copy)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    value = dict(schema='full109-six-original-material-reviews-custody-v1', files=rows,
                 wrappers=wrappers, original_terminal_handles=[51704, 80159, 63478, 36856, 24332, 36854],
                 reviews=6, complete_supplied_union_per_lens=100, fresh_bodies_per_lens=2,
                 unchanged_parent_bodies_identity_reused=346, original_prior_reports=45,
                 conditional_crosslevel_milestone_accepted=True, overall_accepted=False, full_goal_complete=False,
                 root_reconciliation_sha256=digest(reports / 'root-reconciliation-v1.json'))
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), original_files=len(rows), original_reviews=6,
                         conditional_crosslevel_accepted=True, overall_accepted=False)))


if __name__ == '__main__':
    main()
