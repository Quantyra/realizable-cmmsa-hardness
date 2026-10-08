"""Failure-boundary tests; no native mounts, Lean, or cloud operations."""
import tempfile
import unittest
from pathlib import Path
from isolated_cache import CacheMount


class IsolationLifecycle(unittest.TestCase):
    def fixture(self, root, fail=None):
        workspace = root / 'run'; workspace.mkdir()
        warm = root / 'warm'; warm.mkdir()
        calls = []
        def command(argv):
            calls.append(argv)
            return (1 if fail and fail(argv) else 0), '', ''
        return CacheMount(workspace, warm, command=command), calls

    def test_readonly_before_overlay_and_reverse_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            cache, calls = self.fixture(Path(directory))
            cache.open(); cache.close()
            self.assertIn('remount,bind,ro', calls[1])
            self.assertEqual(calls[-2][-1], str(cache.view))
            self.assertEqual(calls[-1][-1], str(cache.root / 'lower'))
            self.assertEqual(cache.mounted, [])

    def test_failed_readonly_setup_unwinds_only_owned_bind(self):
        with tempfile.TemporaryDirectory() as directory:
            cache, calls = self.fixture(Path(directory), lambda a: 'remount,bind,ro' in a)
            with self.assertRaises(RuntimeError): cache.open()
            self.assertEqual(calls[-1], ['sudo', '-n', 'umount', str(cache.root / 'lower')])
            self.assertEqual(cache.mounted, [])
            self.assertFalse(any('overlay' in a for a in calls))

    def test_busy_view_preserves_all_mounts(self):
        with tempfile.TemporaryDirectory() as directory:
            cache, calls = self.fixture(Path(directory), lambda a: 'umount' in a)
            cache.open()
            with self.assertRaises(RuntimeError): cache.close()
            self.assertEqual(len(cache.mounted), 2)
            self.assertEqual(sum('umount' in a for a in calls), 1)

    def test_existing_target_is_not_reused(self):
        with tempfile.TemporaryDirectory() as directory:
            cache, calls = self.fixture(Path(directory))
            cache.view.mkdir()
            with self.assertRaises(FileExistsError): cache.open()
            self.assertEqual(calls, [])


if __name__ == '__main__': unittest.main()
