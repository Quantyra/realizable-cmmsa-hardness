"""Validate both real completed cleanup sets without deleting or invoking cloud."""
import copy
from pathlib import Path
import unittest
from unittest.mock import patch
import full115_cumulative_cleanup_custody_v2 as custody
import full115_cumulative_actual_receipts_v1 as actual


class ActualReceiptBoundary(unittest.TestCase):
    def setUp(self):
        self.rows14 = custody.checked_json(custody.PLAN14, custody.PIN14)['files']
        self.rows18 = custody.checked_json(custody.PLAN18, custody.PIN18)['files']

    def invoke(self, guard, row):
        return guard.reconcile(row['remove'], row['retain_original'], row['sha256'], row['bytes'])

    def test_all32_actual_retained_archives_exact_and_honest(self):
        guard = actual.configured_guard()
        for row in self.rows14 + self.rows18:
            self.assertFalse(Path(row['remove']).exists())
            result = self.invoke(guard, row)
            self.assertEqual(result['current_retained_copies_verified'], 1)
            self.assertFalse(result['new_two_copy_custody'])

    def test_missing18_binding_remains_rejected_after_real_cleanup(self):
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            self.invoke(custody.CumulativeCustody(), self.rows18[0])

    def test_wrong_actual_receipt_bytes_with_matching_fields_rejected(self):
        original = custody.custody_checks.digest
        def digest(path):
            return '0' * 64 if Path(path).resolve() == actual.ADDITIONAL_PATH.resolve() else original(path)
        with patch.object(custody.custody_checks, 'digest', digest), self.assertRaises(ValueError):
            self.invoke(actual.configured_guard(), self.rows18[0])

    def test_unapproved_receipt_rejected_even_with_injected_matching_digest(self):
        original = custody.checked_json
        def checked(path, pin):
            result = original(path, pin)
            if Path(path).resolve() == actual.ADDITIONAL_PATH.resolve():
                result['authorization_received'] = False
            return result
        with patch.object(custody, 'checked_json', checked), self.assertRaises(ValueError):
            self.invoke(actual.configured_guard(), self.rows18[0])

    def test_wrong_retained_path_rejected(self):
        row = dict(self.rows18[0], retain_original=self.rows18[1]['retain_original'])
        with self.assertRaises(ValueError):
            self.invoke(actual.configured_guard(), row)

    def test_changed_retained_complete_bytes_rejected(self):
        original = custody.custody_checks.digest
        def digest(path):
            return '0' * 64 if Path(path).resolve() == Path(self.rows18[0]['retain_original']).resolve() else original(path)
        with patch.object(custody.custody_checks, 'digest', digest), self.assertRaises(ValueError):
            self.invoke(actual.configured_guard(), self.rows18[0])

    def test_truncated_actual_receipt_rejected(self):
        original = custody.checked_json
        def checked(path, pin):
            result = original(path, pin)
            if Path(path).resolve() == actual.ADDITIONAL_PATH.resolve():
                result['files'].pop()
            return result
        with patch.object(custody, 'checked_json', checked), self.assertRaises(ValueError):
            self.invoke(actual.configured_guard(), self.rows18[0])
