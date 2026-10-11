"""Copy only settled continuation evidence, preserving every original byte."""
from datetime import datetime, timezone
import json
from pathlib import Path
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).parent


def main():
    target = HERE/('full109-resume-checkpoint-v2-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    folders = [ROOT/'consumption-v3/settled-cache-recovery-boot-v2',
               ROOT/'local-custody-directory-compression-v1', ROOT/'local-custody-stdout-compression-v2',
               ROOT/'trace-resource-inspections-v1/20261011T001416872136Z',
               ROOT/'trace-resource-inspections-v1/20261011T001559709024Z',
               ROOT/'trace-recovery-progress-v2/20261011T002036833374Z']
    actions = []
    for path in sorted((ROOT/'research-resume-20261010').glob('*/command.json')):
        record = json.loads(path.read_bytes())
        if 'native_exit' in record:
            assert digest(path.parent/'stdout') == record['stdout_sha256']
            assert digest(path.parent/'stderr') == record['stderr_sha256']
            folders.append(path.parent)
            actions.append(dict(command=str(path), native_exit=record['native_exit'], pid=record['pid']))
    for number in range(84, 90):
        folder = HERE/f'full109-trace-small-plan-native{number}-record-v1'
        index = json.loads((folder/'index.json').read_bytes())
        for row in index['records']:
            assert digest(folder/row['target']) == digest(row['source']) == row['sha256']
        folders.append(folder)
    paths = [p for folder in folders for p in sorted(folder.rglob('*')) if p.is_file()]
    paths += [ROOT/'consumption-v3/pending-plans-revalidation-v2.json',
              HERE/'audit_full109_trace_cache_small_v1.py', HERE/'preserve_full109_trace_cache_phase_v1.py']
    assert len(paths) == len(set(paths))
    rows = []
    for i, source in enumerate(paths):
        data = source.read_bytes()
        dest = target/f'{i:03d}-{source.name}'
        dest.open('xb').write(data)
        assert digest(source) == digest(dest)
        rows.append(dict(original=str(source), copy=dest.name, bytes=len(data), sha256=digest(dest)))
    index = dict(files=rows, settled_actions=actions, inherited_worktree_files_copied_without_staging_originals=True,
                 compiler_invoked=False, trace_executed=False, accepted=False,
                 limitations=['Live recovery stdout/receipts are excluded until terminal.',
                              'Initial shell alias/import and timestamp collision failures did not invoke a cloud action; their tool observations are not reconstructed as raw stdout.'])
    (target/'index.json').write_text(json.dumps(index, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(target), complete_original_files=len(rows))))


if __name__ == '__main__':
    main()
