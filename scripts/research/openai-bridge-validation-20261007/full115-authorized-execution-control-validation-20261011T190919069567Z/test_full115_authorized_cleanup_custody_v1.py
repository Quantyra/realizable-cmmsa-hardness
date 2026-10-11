"""Reject unauthorized historical custody substitutions without modifying archives."""
import json
from pathlib import Path
import unittest
from unittest.mock import patch
import full115_authorized_cleanup_custody_v1 as adapter


class CleanupBoundary(unittest.TestCase):
    def setUp(self):
        self.row = json.loads((adapter.FOLDER / 'approved-plan.json').read_bytes())['files'][-5]

    def call(self):
        r = self.row
        return adapter.reconcile(r['remove'], r['retain_original'], r['sha256'], r['bytes'])

    def test_one_retained_copy_explicit(self):
        self.assertEqual(self.call()['current_retained_copies_verified'], 1)
        self.assertFalse(self.call()['new_two_copy_custody'])

    def test_wrong_plan_pin(self):
        with patch.object(adapter, 'PLAN_PIN', '0' * 64), self.assertRaises(AssertionError):
            self.call()

    def test_foreign_path(self):
        with self.assertRaises((AssertionError, StopIteration)):
            adapter.reconcile('C:/a8gcp/not-approved.tar.gz', self.row['retain_original'], self.row['sha256'], self.row['bytes'])

    def test_changed_retained_bytes(self):
        original = adapter.custody_checks.digest
        def altered(path):
            return '0' * 64 if Path(path).resolve() == Path(self.row['retain_original']).resolve() else original(path)
        with patch.object(adapter.custody_checks, 'digest', altered), self.assertRaises(AssertionError):
            self.call()

    def authorization_mutation(self, missing):
        original = adapter.json.loads
        def altered(raw, *args, **kwargs):
            value = original(raw, *args, **kwargs)
            if isinstance(value, dict) and 'authorization' in value:
                if missing:
                    value.pop('authorization')
                else:
                    value['authorization'] = 'not approved'
            return value
        with patch.object(adapter.json, 'loads', altered), self.assertRaises((AssertionError, KeyError)):
            self.call()

    def test_missing_authorization(self):
        self.authorization_mutation(True)

    def test_wrong_authorization(self):
        self.authorization_mutation(False)
