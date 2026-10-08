import json
from pathlib import Path
import tempfile
import unittest
from shared_idle import observe


class IdleObservation(unittest.TestCase):
    def fixture(self, root):
        registry, state, proc = [root / name for name in ('registry', 'state', 'proc')]
        for directory in (registry, state, proc): directory.mkdir()
        (state / 'last-active').write_text('1000\n')
        (registry / 'controller-inventory.json').write_text(json.dumps(
            {'complete': True, 'all_controllers_lease_aware': True}))
        return registry, state, proc

    def test_idle_threshold_is_not_reset_each_poll(self):
        with tempfile.TemporaryDirectory() as directory:
            registry, state, proc = self.fixture(Path(directory))
            first = observe(registry, state, now=2000, proc_root=proc, sessions=[])
            second = observe(registry, state, now=3700, proc_root=proc, sessions=[])
            self.assertFalse(first['idle_threshold_met'])
            self.assertTrue(second['idle_threshold_met'])
            self.assertEqual((state / 'last-active').read_text(), '1000\n')

    def test_native_workload_resets_clock(self):
        with tempfile.TemporaryDirectory() as directory:
            registry, state, proc = self.fixture(Path(directory))
            pid = proc / '42'; pid.mkdir()
            (pid / 'comm').write_text('lean\n'); (pid / 'cmdline').write_bytes(b'lean\0module.lean\0')
            result = observe(registry, state, now=4000, proc_root=proc, sessions=[])
            self.assertFalse(result['idle_threshold_met'])
            self.assertEqual(result['unregistered_workloads'], [{'pid': 42, 'name': 'lean'}])
            self.assertEqual((state / 'last-active').read_text(), '4000\n')

    def test_missing_inventory_never_authorizes_shutdown(self):
        with tempfile.TemporaryDirectory() as directory:
            registry, state, proc = self.fixture(Path(directory))
            (registry / 'controller-inventory.json').unlink()
            result = observe(registry, state, now=4000, proc_root=proc, sessions=[])
            self.assertTrue(result['idle_threshold_met'])
            self.assertFalse(result['controller_inventory_complete'])
            self.assertFalse(result['all_controllers_lease_aware'])

    def test_interactive_session_resets_clock(self):
        with tempfile.TemporaryDirectory() as directory:
            registry, state, proc = self.fixture(Path(directory))
            result = observe(registry, state, now=4000, proc_root=proc, sessions=['research ssh'])
            self.assertFalse(result['idle_threshold_met'])
            self.assertEqual((state / 'last-active').read_text(), '4000\n')


if __name__ == '__main__': unittest.main()
