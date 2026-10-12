"""Disjoint fail-closed adapter preparation; no pending authorization is supplied."""
from dataclasses import dataclass
from pathlib import Path
import full115_cumulative_actual_receipts_v1 as prior
from full115_cumulative_cleanup_custody_v2 import checked_json, VM_ID, ORIGINAL
import custody_checks

HERE = Path(__file__).resolve().parent
PLAN = HERE / 'full118-settled-duplicate-archive-cleanup-plan-v1/plan.json'
PLAN_PIN = '78D9D0ABD067A0D1B55F68B2937E7453CE945E5A0D27B17B7B1CCD64C7D60486'


@dataclass(frozen=True)
class ActualReceipt:
    path: Path
    sha256: str
    authorization: str

    def __post_init__(self):
        if not Path(self.path).resolve().is_relative_to(HERE):
            raise ValueError('Receipt must be retained on the evidence surface')
        if not self.authorization.strip():
            raise ValueError('Actual explicit authorization text required')
        # Validate the complete receipt bytes now; this never creates them.
        checked_json(self.path, self.sha256)


class Pending39Custody:
    def __init__(self, actual=None):
        if actual is not None and not isinstance(actual, ActualReceipt):
            raise TypeError('An actual complete pinned receipt is required')
        self.actual = actual
        self.prior = prior.configured_guard()

    def documents(self):
        plan = checked_json(PLAN, PLAN_PIN)
        if plan['count'] != 39 or len(plan['files']) != 39 or plan['total_bytes'] != 509908701:
            raise ValueError('Frozen 39-file plan scope changed')
        if self.actual is None:
            raise ValueError('Pending 39-file cleanup has no actual authorized receipt')
        receipt = checked_json(self.actual.path, self.actual.sha256)
        if (receipt.get('authorization') != self.actual.authorization or
                receipt.get('authorization_received') is not True or
                receipt.get('files_deleted') is not True or
                receipt.get('only_exact_approved_files') is not True or
                receipt.get('approved_plan_sha256') != PLAN_PIN):
            raise ValueError('Complete exact actual authorization and deletion receipt required')
        approved = {Path(r['remove']).resolve(): r for r in plan['files']}
        completed = {Path(r['removed']).resolve(): r for r in receipt['files']}
        if len(approved) != 39 or len(completed) != 39 or len(receipt['files']) != 39 or set(approved) != set(completed):
            raise ValueError('Receipt must cover exactly all frozen paths')
        for path, row in approved.items():
            done = completed[path]
            if (path.exists() or
                    Path(done['retained']).resolve() != Path(row['retain_complete_native_archive']).resolve() or
                    done['sha256'] != row['sha256'] or type(done['bytes']) is not int or done['bytes'] != row['bytes'] or
                    done.get('retained_verified_after') is not True or
                    done.get('retained_archive_sha256') != row['retained_archive_sha256'] or
                    done.get('retained_member_sha256') != row['retained_member_sha256']):
                raise ValueError('Actual deletion receipt differs from exact frozen row')
        return approved, receipt

    def reconcile(self, short_path, repository_path, remote_sha256, remote_bytes):
        short, retained = Path(short_path), Path(repository_path)
        plan = checked_json(PLAN, PLAN_PIN)
        new = {Path(r['remove']).resolve(): r for r in plan['files'] if r['kind'] == 'short_complete_native_duplicate'}
        if short.exists() or short.resolve() not in new:
            return self.prior.reconcile(short, retained, remote_sha256, remote_bytes)
        approved, _ = self.documents()
        row = approved[short.resolve()]
        if (short.resolve().parent != Path('C:/a8gcp').resolve() or
                retained.resolve() != Path(row['retain_complete_native_archive']).resolve() or
                remote_sha256 != row['sha256'] or type(remote_bytes) is not int or remote_bytes != row['bytes']):
            raise ValueError('Exact current custody path and archive identities required')
        terminal = checked_json(row['terminal_receipt'], row['terminal_receipt_sha256'])
        stop = checked_json(row['independent_stop'], row['independent_stop_sha256'])
        historical = terminal['custody']
        if (terminal['run'] != row['run'] or stop['run'] != row['run'] or
                terminal['terminal']['native_terminal'] is not True or stop['independent']['status'] != 'TERMINATED' or
                str(stop['independent']['id']) != VM_ID or
                Path(historical['short_path']).resolve() != short.resolve() or
                Path(historical['repository_path']).resolve() != retained.resolve() or
                historical['remote_sha256'] != remote_sha256 or historical['bytes'] != remote_bytes):
            raise ValueError('Historical native terminal or exact custody identity changed')
        if retained.stat().st_size != remote_bytes or custody_checks.digest(retained) != remote_sha256:
            raise ValueError('Retained complete original archive bytes changed')
        return dict(short_path=str(short), repository_path=str(retained), remote_sha256=remote_sha256,
                    repository_sha256=remote_sha256, bytes=remote_bytes, current_retained_copies_verified=1,
                    new_two_copy_custody=False, historical_two_copy_receipt_preserved=True,
                    short_copy_removed_with_explicit_authorization=True,
                    authorized_cleanup_plan_sha256=PLAN_PIN, authorized_cleanup_receipt_sha256=self.actual.sha256)


def activate(actual):
    # No default or current production configuration is installed for the pending set.
    guard = Pending39Custody(actual)
    guard.documents()
    if custody_checks.verify_local_custody is not ORIGINAL:
        raise ValueError('Another custody adapter is already installed')
    custody_checks.verify_local_custody = guard.reconcile
    return guard
