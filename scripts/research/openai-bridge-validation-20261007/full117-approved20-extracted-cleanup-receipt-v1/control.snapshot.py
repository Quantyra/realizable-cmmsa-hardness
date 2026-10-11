"""Execute only the exactly approved twenty settled extracted duplicates."""
import hashlib
import json
import shutil
import subprocess
import tarfile
from pathlib import Path
from prepare_full117_extracted_package_cleanup_plan_v1 import checked, BASE

H = Path(__file__).resolve().parent
PIN = '3D554210BD7BF8285121A3D8C36C765B0CEEDECECF1A4F4ABFE4608D652BF0BF'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest().upper()

def verify(row, removed=False):
    target = Path(row['remove'])
    retained = checked(Path(row['retain_complete_native_archive']))
    assert target.absolute().is_relative_to(BASE) and target.name == 'package-sources.tar.gz'
    if removed:
        assert not target.exists()
    else:
        checked(target)
        assert target.stat().st_size == row['bytes'] and sha(target) == row['sha256']
    assert retained.stat().st_size == row['retained_archive_bytes']
    assert sha(retained) == row['retained_archive_sha256']
    for field, pin in [('terminal_receipt', 'terminal_receipt_sha256'), ('independent_stop', 'independent_stop_sha256')]:
        assert sha(checked(Path(row[field]))) == row[pin]
    with tarfile.open(retained, 'r:gz') as archive:
        members = archive.getmembers()
        assert len(members) == row['native_archive_members']
        assert len({m.name for m in members}) == len(members) and all(m.isfile() for m in members)
        raw = archive.extractfile(row['retained_member']).read()
        assert len(raw) == row['retained_member_bytes']
        assert hashlib.sha256(raw).hexdigest().upper() == row['retained_member_sha256'] == row['sha256']
        owner = json.loads(archive.extractfile('dedicated-worker-terminal.json').read())
        assert owner['run'] == row['run'] and str(owner['host']['id']) == '7237681467779354904'
    assert sha(retained) == row['retained_archive_sha256']

def main():
    plan = H / 'full117-settled-extracted-package-archive-cleanup-plan-v1/plan.json'
    assert sha(plan) == PIN
    value = json.loads(plan.read_bytes())
    assert len(value['files']) == 20 and sum(r['bytes'] for r in value['files']) == 561073700
    folder = H / 'full117-approved20-extracted-cleanup-receipt-v1'
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_bytes(b'* -text\n')
    (folder / 'plan.json').write_bytes(plan.read_bytes())
    authorization = dict(actual_reply='Approve these 20 extracted duplicates',
        question_item_id=['request_user_input_async', 'call_ecb6abe9d74743d8bcb4bb9e3a4bf52f', 0],
        relayed_by='/root', plan_sha256=PIN, count=20, total_bytes=561073700, authorization_received=True)
    (folder / 'authorization.json').write_text(json.dumps(authorization, indent=2) + '\n', encoding='utf-8')
    (folder / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (folder / 'remove.snapshot.ps1').write_bytes((H / 'remove_full117_exact_approved_single_file_v1.ps1').read_bytes())
    before = shutil.disk_usage(BASE).free
    for row in value['files']:
        verify(row)
    receipts = []
    for row in value['files']:
        verify(row)
        command = ['powershell.exe', '-NoProfile', '-NonInteractive', '-File',
            str(H / 'remove_full117_exact_approved_single_file_v1.ps1'), '-TargetPath', row['remove'],
            '-ExpectedSha', row['sha256'], '-ExpectedBytes', str(row['bytes'])]
        result = subprocess.run(command, capture_output=True)
        (folder / f"remove-{row['number']}.stdout").write_bytes(result.stdout)
        (folder / f"remove-{row['number']}.stderr").write_bytes(result.stderr)
        assert result.returncode == 0, result.stderr.decode(errors='replace')
        verify(row, removed=True)
        receipt = dict(path=row['remove'], deleted_bytes=row['bytes'], native_exit=0,
            retained_archive_sha256=row['retained_archive_sha256'], retained_member_sha256=row['sha256'], verified_after=True)
        receipts.append(receipt)
        with (folder / 'journal.jsonl').open('a', encoding='utf-8') as journal:
            journal.write(json.dumps(receipt) + '\n')
            journal.flush()
    for row in value['files']:
        verify(row, removed=True)
    receipt = dict(authorization_sha256=sha(folder / 'authorization.json'), plan_sha256=PIN,
        files=receipts, count=20, total_bytes=561073700, free_before=before, free_after=shutil.disk_usage(BASE).free,
        all_retained_complete_archives_unchanged=True, whole_native_archive_custody_unchanged=True,
        prior32_cleanup_scope_unchanged=True, compiler_invoked=False, cloud_operation=False)
    (folder / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(receipt=str(folder / 'receipt.json'), receipt_sha256=sha(folder / 'receipt.json'),
        free_after=receipt['free_after'])), flush=True)

if __name__ == '__main__':
    main()
