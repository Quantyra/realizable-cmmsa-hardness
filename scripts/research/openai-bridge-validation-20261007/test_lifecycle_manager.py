import tempfile
import unittest
from pathlib import Path
from lifecycle_manager import drain_and_act
from thread_leases import acquire, release, Busy, phase


def idle():
    return {'process_scan_complete': True, 'session_scan_complete': True,
            'controller_inventory_complete': True, 'all_controllers_lease_aware': True,
            'idle_threshold_met': True, 'unregistered_workloads': [], 'interactive_sessions': []}


class ManagerSafety(unittest.TestCase):
    def test_lease_blocks_before_observation_or_action(self):
        with tempfile.TemporaryDirectory() as root:
            acquire(root, 'alpha', 'run_alpha')
            with self.assertRaises(Busy):
                drain_and_act(root, observe=lambda: self.fail('Observed with active lease'),
                              action=lambda _: self.fail('Shutdown with active lease'))
            self.assertEqual(phase(Path(root)), 'ACCEPTING')

    def test_observation_and_action_hold_admission_lock(self):
        with tempfile.TemporaryDirectory() as root:
            def observe():
                with self.assertRaises(Busy): acquire(root, 'beta', 'run_beta')
                return idle()
            def action(observation):
                self.assertEqual(phase(Path(root)), 'DRAINING')
                with self.assertRaises(Busy): acquire(root, 'beta', 'run_beta')
                return 'simulated manager action'
            self.assertEqual(drain_and_act(root, observe=observe, action=action), 'simulated manager action')
            with self.assertRaises(Busy): acquire(root, 'beta', 'run_beta')

    def test_incomplete_or_foreign_work_refuses_shutdown(self):
        for key, value in [('process_scan_complete', False), ('session_scan_complete', False),
                           ('controller_inventory_complete', False), ('all_controllers_lease_aware', False),
                           ('idle_threshold_met', False), ('unregistered_workloads', ['foreign pid']),
                           ('interactive_sessions', ['ssh']), ('unregistered_workloads', None)]:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as root:
                observation = idle(); observation[key] = value
                with self.assertRaises(Busy):
                    drain_and_act(root, observe=lambda: observation, action=lambda _: self.fail('Unsafe shutdown'))
                self.assertEqual(phase(Path(root)), 'ACCEPTING')

    def test_failed_action_stays_draining(self):
        with tempfile.TemporaryDirectory() as root:
            def action(_): raise RuntimeError('Uncertain shutdown result')
            with self.assertRaises(RuntimeError): drain_and_act(root, observe=idle, action=action)
            self.assertEqual(phase(Path(root)), 'DRAINING')
            with self.assertRaises(Busy): acquire(root, 'beta', 'run_beta')

    def test_incomplete_lease_blocks_manager(self):
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / 'active' / 'incomplete').mkdir(parents=True)
            with self.assertRaises(Busy):
                drain_and_act(root, observe=idle, action=lambda _: self.fail('Incomplete lease ignored'))


if __name__ == '__main__': unittest.main()
