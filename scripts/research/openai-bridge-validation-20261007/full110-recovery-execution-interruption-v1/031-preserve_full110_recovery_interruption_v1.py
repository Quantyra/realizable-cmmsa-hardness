"""Preserve terminal controller failure after two successful remote operations."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
WRAPPER = ROOT / 'research-resume-20261011/20261011T032930698566Z-1587aaca7c15'
OPERATION = ROOT / 'settled-cache-recovery-v1/20261011T033104479357Z'


def main():
    command = json.loads((WRAPPER / 'command.json').read_bytes())
    assert command['native_exit'] == 1 and command['pid'] == 12852
    for stream in ('stdout', 'stderr'):
        assert digest(WRAPPER / stream) == command[stream + '_sha256']
    commands = json.loads((OPERATION / 'commands.json').read_bytes())
    assert len(commands) == 10
    for row in commands:
        for stream in ('stdout', 'stderr'):
            assert digest(OPERATION / row[stream + '_path']) == row[stream + '_sha256']
        assert not row['timed_out']
    assert [row['native_exit'] for row in commands] == [0] * 9 + [3221225477]
    assert commands[8]['argv'][5] == '--command=python3 -B /home/dfredriksen_quantyra_org/full110-settled-cache-native90-v1/full110_settled_cache_native90_v1.py --execute'
    assert commands[9]['argv'][5] == '--command=sha256sum /home/dfredriksen_quantyra_org/full110-settled-cache-native90-v1/receipt.json'
    remote90 = json.loads((OPERATION / 'control/008.stdout').read_bytes())
    assert remote90['receipt_sha256'] == '18722833D18CC01D6C14D35ED74424B1E872C98576A87F62E62BEBD1BA5386CE'
    assert remote90['repointed_files'] == 19233 and not remote90['compiler_invoked']
    assert (OPERATION / 'control/009.stdout').read_text().split()[0].upper() == remote90['receipt_sha256']
    assert not (OPERATION / '90-receipt.json').exists()
    paths = {Path(__file__).resolve()}
    for folder in (WRAPPER, OPERATION):
        paths.update(p for p in folder.rglob('*') if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-recovery-execution-interruption-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for number, path in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + path.name)
        copy.open('xb').write(path.read_bytes())
        assert digest(copy) == digest(path)
        rows.append(dict(original=str(path), copy=copy.name, bytes=path.stat().st_size, sha256=digest(path)))
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(dict(
        files=rows, original_handle=50622, original_exit=1, remote_successful_scopes=[110, 90],
        collected_receipts=[110], scope90_terminal_stdout=remote90, scope90_receipt_collection_pending=True,
        failed_action='read-only remote receipt SHA collection', failed_native_exit=3221225477,
        remaining_scopes_not_attempted=[91, 92, 93, 94, 95], no_execution_replay=True,
        compiler_invoked=False, mathematical_acceptance=False), indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), complete_original_files=len(rows),
                         original_failure_preserved=True, remaining_scopes=[91, 92, 93, 94, 95])), flush=True)


if __name__ == '__main__':
    main()
