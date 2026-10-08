import unittest
from shared_controller import admission_ready, cloud_operation_allowed


class ControllerBoundaries(unittest.TestCase):
    def test_vm_power_and_resource_mutations_rejected(self):
        for action in ('start', 'stop', 'delete', 'create', 'set-machine-type', 'reset'):
            with self.subTest(action=action), self.assertRaises(ValueError):
                cloud_operation_allowed(['compute', 'instances', action, 'quantyra-lean-builder-01'])
        cloud_operation_allowed(['compute', 'instances', 'describe', 'quantyra-lean-builder-01'])

    def test_ready_record_without_verified_effective_manager_is_refused(self):
        readiness = {'ready': True, 'vm_id': '8337954477286097405', 'controller_inventory_complete': True,
                     'all_controllers_lease_aware': True, 'enrolled_threads': ['alpha']}
        self.assertFalse(admission_ready(readiness, {'thread': 'alpha'}, False))
        self.assertTrue(admission_ready(readiness, {'thread': 'alpha'}, True))
        self.assertFalse(admission_ready(readiness, {'thread': 'beta'}, True))

    def test_missing_unknown_or_substring_enrollment_is_refused(self):
        for readiness in ({}, [], None, {'ready': True}):
            self.assertFalse(admission_ready(readiness, {'thread': 'alpha'}, True))
        readiness = {'ready': True, 'vm_id': '8337954477286097405', 'controller_inventory_complete': True,
                     'all_controllers_lease_aware': True, 'enrolled_threads': 'alpha'}
        self.assertFalse(admission_ready(readiness, {'thread': 'alpha'}, True))


if __name__ == '__main__': unittest.main()
