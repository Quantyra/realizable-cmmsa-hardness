"""Fail-closed historical custody after separately authorized exact-copy cleanups.

The original two-copy helper and its historical failures remain unchanged.
The second plan is pending: no receipt or approval is inferred from its presence.
Only an explicitly supplied, complete, pinned receipt can enable that plan.
"""
from dataclasses import dataclass
import json
from pathlib import Path
import re
import custody_checks

HERE = Path(__file__).resolve().parent
VM_ID = '7237681467779354904'
ORIGINAL = custody_checks.verify_local_custody
PLAN14 = HERE / 'full115-authorized-short-cleanup-20261011T1902419364615Z/approved-plan.json'
PIN14 = '670FCEA3C0BED82BE8371A3169328353FD0290C18A1FF4C308899C5E59C7B2AD'
RECEIPT14 = PLAN14.parent / 'receipt.json'
RECEIPT14_PIN = '6DD692CC79AD3C39348C6F1767BC7F1ECFA9305AC9AFDC438BF8A61B1D42F502'
AUTH14 = 'Explicit user reply: Approve the 14-file cleanup; relayed by root'
PLAN18 = HERE / 'full115-next-redundant-native-cleanup-plan-v1/plan.json'
PIN18 = '7F5239118274572A666B753D7B3D57356D9636E378ACE06E2B90E860351BCF1F'


def checked_json(path, pin):
    if not re.fullmatch(r'[A-F0-9]{64}', pin):
        raise ValueError('Exact uppercase SHA-256 required')
    if custody_checks.digest(path) != pin:
        raise ValueError('Frozen document bytes changed')
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


@dataclass(frozen=True)
class AdditionalReceipt:
    """Caller must supply these actual values after explicit user authorization.

    A future receipt uses the first receipt's row schema plus literal booleans
    authorization_received=True and files_deleted=True, and the actual user
    authorization text must match authorization exactly. No value is supplied
    for the pending 18-file cleanup by this module.
    """
    path: Path
    sha256: str
    authorization: str

    def __post_init__(self):
        if not Path(self.path).resolve().is_relative_to(HERE):
            raise ValueError('Additional receipt must be retained in this evidence surface')
        if not re.fullmatch(r'[A-F0-9]{64}', self.sha256):
            raise ValueError('Additional complete receipt SHA-256 required')
        if not isinstance(self.authorization, str) or not self.authorization.strip():
            raise ValueError('Actual explicit authorization text required')


class CumulativeCustody:
    def __init__(self, additional=None):
        if additional is not None and not isinstance(additional, AdditionalReceipt):
            raise TypeError('Explicit frozen additional receipt required')
        self.additional = additional

    def documents(self, short):
        plan14 = checked_json(PLAN14, PIN14)
        plan18 = checked_json(PLAN18, PIN18)
        maps = []
        for plan, count, total in ((plan14, 14, 555670409), (plan18, 18, 714067101)):
            if len(plan['files']) != count or plan['total_bytes'] != total:
                raise ValueError('Frozen approved-set scope changed')
            rows = {Path(r['remove']).resolve(): r for r in plan['files']}
            if len(rows) != count:
                raise ValueError('Duplicate cleanup path')
            if any(p.parent != Path('C:/a8gcp').resolve() for p in rows):
                raise ValueError('Cleanup target escapes exact short-copy directory')
            maps.append(rows)
        if set(maps[0]) & set(maps[1]):
            raise ValueError('The two cleanup sets overlap')
        if short in maps[0]:
            receipt = checked_json(RECEIPT14, RECEIPT14_PIN)
            if receipt.get('authorization') != AUTH14 or receipt.get('full114_excluded') is not True:
                raise ValueError('Original exact 14-file authorization changed')
            return maps[0], receipt, PIN14, RECEIPT14_PIN
        if short in maps[1]:
            if self.additional is None:
                raise ValueError('Additional 18-file cleanup is not authorized and frozen')
            receipt = checked_json(self.additional.path, self.additional.sha256)
            if (receipt.get('authorization') != self.additional.authorization or
                    receipt.get('authorization_received') is not True or
                    receipt.get('files_deleted') is not True):
                raise ValueError('Complete explicit additional authorization/cleanup receipt required')
            return maps[1], receipt, PIN18, self.additional.sha256
        raise ValueError('Missing copy is outside both exact frozen cleanup sets')

    def reconcile(self, short_path, repository_path, remote_sha256, remote_bytes):
        short, retained = Path(short_path), Path(repository_path)
        if short.exists():
            return ORIGINAL(short, retained, remote_sha256, remote_bytes)
        if not re.fullmatch(r'[A-F0-9]{64}', remote_sha256):
            raise ValueError('Invalid remote SHA-256')
        if type(remote_bytes) is not int or remote_bytes <= 0:
            raise ValueError('Invalid remote archive size')
        plans, receipt, plan_pin, receipt_pin = self.documents(short.resolve())
        if receipt.get('approved_plan_sha256') != plan_pin or receipt.get('only_exact_approved_files') is not True:
            raise ValueError('Receipt does not bind the exact approved plan')
        rows = {Path(r['removed']).resolve(): r for r in receipt['files']}
        if len(rows) != len(receipt['files']) or set(rows) != set(plans):
            raise ValueError('Receipt must cover the full exact approved set without duplicates')
        for path, approved in plans.items():
            completed = rows[path]
            if (Path(completed['retained']).resolve() != Path(approved['retain_original']).resolve() or
                    completed['sha256'] != approved['sha256'] or
                    type(completed['bytes']) is not int or completed['bytes'] != approved['bytes'] or
                    completed.get('retained_verified_after') is not True):
                raise ValueError('Cleanup receipt row differs from frozen plan')
        approved = plans[short.resolve()]
        if (retained.resolve() != Path(approved['retain_original']).resolve() or
                remote_sha256 != approved['sha256'] or remote_bytes != approved['bytes']):
            raise ValueError('Historical custody paths or identities differ from approved pair')
        terminal = checked_json(approved['terminal_receipt'], approved['terminal_receipt_sha256'])
        stop = checked_json(approved['independent_stop'], approved['independent_stop_sha256'])
        if (terminal['run'] != approved['run'] or stop['run'] != approved['run'] or
                terminal['terminal']['native_terminal'] is not True or
                stop['independent']['status'] != 'TERMINATED' or
                str(stop['independent']['id']) != VM_ID):
            raise ValueError('Historical exact-resource terminal evidence changed')
        archived = terminal['custody']
        if (Path(archived['short_path']).resolve() != short.resolve() or
                Path(archived['repository_path']).resolve() != retained.resolve() or
                archived['remote_sha256'] != remote_sha256 or archived['bytes'] != remote_bytes):
            raise ValueError('Original custody receipt does not bind the approved pair')
        if retained.stat().st_size != remote_bytes or custody_checks.digest(retained) != remote_sha256:
            raise ValueError('Retained complete original archive changed')
        return dict(short_path=str(short), repository_path=str(retained), remote_sha256=remote_sha256,
                    repository_sha256=remote_sha256, bytes=remote_bytes,
                    historical_two_copy_receipt_preserved=True,
                    short_copy_removed_with_explicit_authorization=True,
                    current_retained_copies_verified=1, new_two_copy_custody=False,
                    authorized_cleanup_plan_sha256=plan_pin,
                    authorized_cleanup_receipt_sha256=receipt_pin)


def activate(additional=None):
    if custody_checks.verify_local_custody is not ORIGINAL:
        raise ValueError('Another custody adapter is already installed')
    guard = CumulativeCustody(additional)
    custody_checks.verify_local_custody = guard.reconcile
    return guard
