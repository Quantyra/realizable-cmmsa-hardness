import unittest,tempfile
from pathlib import Path
from thread_leases import acquire,release,manager_drain,Busy,OwnershipError
class LeaseSafety(unittest.TestCase):
    def test_two_threads_and_no_foreign_release(self):
        with tempfile.TemporaryDirectory() as d:
            acquire(d,'alpha','run_alpha');acquire(d,'beta','run_beta')
            with self.assertRaises(Busy):acquire(d,'alpha','duplicate')
            with self.assertRaises(OwnershipError):release(d,'alpha','run_beta',native_terminal=True,custody_verified=True)
            release(d,'alpha','run_alpha',native_terminal=True,custody_verified=True)
            with self.assertRaises(Busy):
                with manager_drain(d,observed_unregistered_workloads=[]):self.fail('Stopped beta')
            self.assertTrue((Path(d)/'active/beta/owner.json').exists())
            self.assertTrue((Path(d)/'completed/run_alpha/terminal-custody.json').exists())
    def test_custody_required_and_draining_blocks_admission(self):
        with tempfile.TemporaryDirectory() as d:
            acquire(d,'alpha','run_alpha')
            with self.assertRaises(Busy):release(d,'alpha','run_alpha',native_terminal=True,custody_verified=False)
            release(d,'alpha','run_alpha',native_terminal=True,custody_verified=True)
            with manager_drain(d,observed_unregistered_workloads=[]):
                with self.assertRaises(Busy):acquire(d,'beta','run_beta')
            with self.assertRaises(Busy):acquire(d,'beta','run_beta')
    def test_empty_registry_is_not_idle_proof(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(Busy):
                with manager_drain(d,observed_unregistered_workloads=['foreign_pid']):self.fail('Stopped unknown workload')
if __name__=='__main__':unittest.main()
