"""Synthetic future-receipt tests; no approval, receipt file, deletion or cloud action.

Future receipts exist only as mocked in-memory dictionaries. They are never
written to an authoritative cleanup path or used to activate a live controller.
"""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch
import full115_cumulative_cleanup_custody_v2 as adapter


class CumulativeCleanupBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan14 = adapter.checked_json(adapter.PLAN14, adapter.PIN14)
        cls.plan18 = adapter.checked_json(adapter.PLAN18, adapter.PIN18)
        cls.row14 = cls.plan14['files'][-1]
        cls.row18 = cls.plan18['files'][0]

    def invoke(self, guard, row):
        return guard.reconcile(row['remove'], row['retain_original'], row['sha256'], row['bytes'])

    def synthetic_case(self, mutate=None, pin='1' * 64, row=None):
        row = self.row18 if row is None else row
        synthetic_path = adapter.HERE / 'SYNTHETIC-NOT-WRITTEN-future-receipt.json'
        auth = 'SYNTHETIC UNIT TEST ONLY - NOT USER AUTHORIZATION'
        receipt = dict(approved_plan_sha256=adapter.PIN18, authorization=auth,
                       authorization_received=True, files_deleted=True, only_exact_approved_files=True,
                       files=[dict(removed=r['remove'], retained=r['retain_original'],
                                   bytes=r['bytes'], sha256=r['sha256'], retained_verified_after=True)
                              for r in self.plan18['files']])
        if mutate:
            mutate(receipt)
        actual_checked, actual_exists = adapter.checked_json, Path.exists

        def checked(path, supplied_pin):
            if Path(path).resolve() == synthetic_path.resolve():
                if supplied_pin != '1' * 64:
                    raise ValueError('Synthetic receipt bytes/pin mismatch')
                return copy.deepcopy(receipt)
            return actual_checked(path, supplied_pin)

        def exists(path):
            return False if path.resolve() == Path(row['remove']).resolve() else actual_exists(path)

        frozen = adapter.AdditionalReceipt(synthetic_path, pin, auth)
        with patch.object(adapter, 'checked_json', checked), patch.object(Path, 'exists', exists):
            return self.invoke(adapter.CumulativeCustody(frozen), row)

    def test_existing_approved14_honest_one_copy(self):
        result = self.invoke(adapter.CumulativeCustody(), self.row14)
        self.assertEqual(result['current_retained_copies_verified'], 1)
        self.assertFalse(result['new_two_copy_custody'])
        self.assertEqual(result['authorized_cleanup_receipt_sha256'], adapter.RECEIPT14_PIN)

    def test_pending18_keeps_original_two_copy_gate(self):
        result = self.invoke(adapter.CumulativeCustody(), self.row18)
        self.assertEqual(result['short_sha256'], self.row18['sha256'])
        self.assertNotIn('short_copy_removed_with_explicit_authorization', result)

    def test_missing_additional_configuration_fails_closed(self):
        original = Path.exists
        def exists(path):
            return False if path.resolve() == Path(self.row18['remove']).resolve() else original(path)
        with patch.object(Path, 'exists', exists), self.assertRaisesRegex(ValueError, 'not authorized'):
            self.invoke(adapter.CumulativeCustody(), self.row18)

    def test_missing_actual_receipt_fails_closed(self):
        config = adapter.AdditionalReceipt(adapter.HERE / 'ABSENT-NOT-WRITTEN.json', '1' * 64, 'test only')
        original = Path.exists
        def exists(path):
            return False if path.resolve() == Path(self.row18['remove']).resolve() else original(path)
        with patch.object(Path, 'exists', exists), self.assertRaises(FileNotFoundError):
            self.invoke(adapter.CumulativeCustody(config), self.row18)

    def test_synthetic_future_success_honest_one_copy(self):
        result = self.synthetic_case()
        self.assertEqual(result['current_retained_copies_verified'], 1)
        self.assertFalse(result['new_two_copy_custody'])
        self.assertEqual(result['authorized_cleanup_plan_sha256'], adapter.PIN18)

    def test_unapproved_future_receipt_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r.update(authorization_received=False))

    def test_wrong_authorization_text_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r.update(authorization='not the supplied authority'))

    def test_incomplete_cleanup_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r.update(files_deleted=False))

    def test_wrong_complete_future_receipt_pin_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(pin='2' * 64)

    def test_wrong14_receipt_bytes_with_matching_fields_rejected(self):
        original = adapter.custody_checks.digest
        def digest(path):
            return '0' * 64 if Path(path).resolve() == adapter.RECEIPT14.resolve() else original(path)
        with patch.object(adapter.custody_checks, 'digest', digest), self.assertRaises(ValueError):
            self.invoke(adapter.CumulativeCustody(), self.row14)

    def test_missing_row_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r['files'].pop())

    def test_duplicate_row_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r['files'].__setitem__(1, copy.deepcopy(r['files'][0])))

    def test_wrong_retained_path_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r['files'][0].update(retained=str(adapter.HERE / 'foreign.tar.gz')))

    def test_wrong_path_in_other_row_rejected(self):
        with self.assertRaises(ValueError):
            self.synthetic_case(lambda r: r['files'][1].update(removed='C:/a8gcp/unapproved.tar.gz'))

    def test_changed_retained_complete_archive_rejected(self):
        original = adapter.custody_checks.digest
        def digest(path):
            return '0' * 64 if Path(path).resolve() == Path(self.row18['retain_original']).resolve() else original(path)
        with patch.object(adapter.custody_checks, 'digest', digest), self.assertRaises(ValueError):
            self.synthetic_case()

    def test_bad_remote_size_rejected(self):
        altered = dict(self.row14, bytes=self.row14['bytes'] + 1)
        with self.assertRaises(ValueError):
            self.invoke(adapter.CumulativeCustody(), altered)

    def test_foreign_historical_resource_rejected(self):
        original = adapter.checked_json
        def checked(path, pin):
            result = original(path, pin)
            if Path(path).resolve() == Path(self.row14['independent_stop']).resolve():
                result['independent']['id'] = 'foreign'
            return result
        with patch.object(adapter, 'checked_json', checked), self.assertRaises(ValueError):
            self.invoke(adapter.CumulativeCustody(), self.row14)

    def test_configuration_requires_pin_and_authorization(self):
        for pin, auth in [('bad', 'text'), ('1' * 64, '')]:
            with self.assertRaises(ValueError):
                adapter.AdditionalReceipt(adapter.HERE / 'NOT-WRITTEN.json', pin, auth)

    def test_configuration_rejects_receipt_path_escape(self):
        with self.assertRaises(ValueError):
            adapter.AdditionalReceipt(adapter.HERE.parent / 'foreign.json', '1' * 64, 'test')
