import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from custody_checks import digest, verify_local_custody, verify_worker_terminal


SPEC = {'thread': 'alpha', 'run': 'run_alpha'}


def fixture(path, *, native=0, failure=None, mounts=True, duplicate=False, wrong_run=False):
    receipt = {'thread': 'alpha', 'run': 'foreign' if wrong_run else 'run_alpha', 'spec': SPEC,
               'host': {'id': '8337954477286097405'}, 'native_exit': native,
               'finish_native_exit': 0, 'failure': failure, 'owned_mounts_released': mounts}
    files = {'shared-worker-terminal.json': json.dumps(receipt).encode(), 'native-exit': str(native).encode(),
             'finish.native-exit': b'0', 'terminal.utc': b'2026-10-08T02:00:00Z'}
    with tarfile.open(path, 'w:gz') as archive:
        for name, data in files.items():
            info = tarfile.TarInfo(name); info.size = len(data); archive.addfile(info, io.BytesIO(data))
        if duplicate:
            info = tarfile.TarInfo('native-exit'); info.size = 1; archive.addfile(info, io.BytesIO(b'0'))


class CustodySafety(unittest.TestCase):
    def test_two_verified_copies_and_red_terminal_are_distinct_from_acceptance(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = [Path(directory) / name for name in ('short.tar.gz', 'repo.tar.gz')]
            fixture(a, native=1); b.write_bytes(a.read_bytes())
            verify_local_custody(a, b, digest(a), a.stat().st_size)
            result = verify_worker_terminal(a, SPEC)
            self.assertTrue(result['native_terminal'])
            self.assertFalse(result['worker_compile_green'])
            self.assertTrue(result['acceptance_audit_and_reviews_required'])

    def test_tampered_copy_and_same_copy_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = [Path(directory) / name for name in ('a', 'b')]
            a.write_bytes(b'archive'); b.write_bytes(b'changed')
            with self.assertRaises(ValueError): verify_local_custody(a, b, digest(a), a.stat().st_size)
            with self.assertRaises(ValueError): verify_local_custody(a, a, digest(a), a.stat().st_size)

    def test_foreign_failure_busy_mount_and_duplicate_terminal_rejected(self):
        for parameters in ({'wrong_run': True}, {'failure': 'cleanup failed'}, {'mounts': False}, {'duplicate': True}):
            with self.subTest(parameters=parameters), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'evidence.tar.gz'; fixture(path, **parameters)
                with self.assertRaises(ValueError): verify_worker_terminal(path, SPEC)

    def test_hardlink_is_not_a_second_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = [Path(directory) / name for name in ('a', 'b')]
            a.write_bytes(b'archive'); b.hardlink_to(a)
            with self.assertRaises(ValueError): verify_local_custody(a, b, digest(a), a.stat().st_size)


if __name__ == '__main__': unittest.main()
