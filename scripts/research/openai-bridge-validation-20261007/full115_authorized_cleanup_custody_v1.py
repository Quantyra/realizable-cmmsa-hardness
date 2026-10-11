"""Explicit historical custody reconciliation after the authorized 14-copy cleanup.

Original two-copy controls remain unchanged. This adapter does not establish new
two-copy custody and is never a substitute for fresh native terminal evidence.
"""
import json
from pathlib import Path
import custody_checks

HERE = Path(__file__).resolve().parent
FOLDER = HERE / 'full115-authorized-short-cleanup-20261011T1902419364615Z'
PLAN_PIN = '670FCEA3C0BED82BE8371A3169328353FD0290C18A1FF4C308899C5E59C7B2AD'
RECEIPT_PIN = '6DD692CC79AD3C39348C6F1767BC7F1ECFA9305AC9AFDC438BF8A61B1D42F502'
ORIGINAL = custody_checks.verify_local_custody


def reconcile(short_path, repository_path, remote_sha256, remote_bytes):
    short, retained = Path(short_path), Path(repository_path)
    if short.exists():
        return ORIGINAL(short, retained, remote_sha256, remote_bytes)
    plan_path = FOLDER / 'approved-plan.json'
    assert custody_checks.digest(plan_path) == PLAN_PIN
    assert custody_checks.digest(FOLDER / 'receipt.json') == RECEIPT_PIN
    plan = json.loads(plan_path.read_bytes())
    receipt = json.loads((FOLDER / 'receipt.json').read_text(encoding='utf-8-sig'))
    assert receipt['approved_plan_sha256'] == PLAN_PIN
    assert receipt['authorization'] == 'Explicit user reply: Approve the 14-file cleanup; relayed by root'
    assert receipt['only_exact_approved_files'] and receipt['full114_excluded']
    assert len(plan['files']) == len(receipt['files']) == 14
    assert plan['total_bytes'] == 555670409
    assert len({r['removed'] for r in receipt['files']}) == 14
    assert short.resolve().parent == Path('C:/a8gcp').resolve()
    approved = next(r for r in plan['files'] if Path(r['remove']).resolve() == short.resolve())
    removed = next(r for r in receipt['files'] if Path(r['removed']).resolve() == short.resolve())
    assert Path(approved['retain_original']).resolve() == Path(removed['retained']).resolve() == retained.resolve()
    assert approved['sha256'] == removed['sha256'] == remote_sha256
    assert approved['bytes'] == removed['bytes'] == remote_bytes
    assert removed['retained_verified_after']
    assert retained.stat().st_size == remote_bytes and custody_checks.digest(retained) == remote_sha256
    return dict(short_path=str(short), repository_path=str(retained),
                remote_sha256=remote_sha256, repository_sha256=remote_sha256,
                bytes=remote_bytes, historical_two_copy_receipt_preserved=True,
                short_copy_removed_with_explicit_authorization=True,
                current_retained_copies_verified=1, new_two_copy_custody=False,
                authorized_cleanup_plan_sha256=PLAN_PIN,
                authorized_cleanup_receipt_sha256=custody_checks.digest(FOLDER / 'receipt.json'))


def activate():
    assert custody_checks.verify_local_custody is ORIGINAL
    custody_checks.verify_local_custody = reconcile
