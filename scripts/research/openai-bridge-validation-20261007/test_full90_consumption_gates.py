"""Negative qualification-boundary fixtures; not kernel or coverage evidence."""
import copy
import unittest
from full90_consumption_controller import require_qualified_green
from prepare_builder02_full90 import REQUEST

class Gates(unittest.TestCase):
    def setUp(self):
        self.native = dict(compile_green=True)
        self.qualified = dict(full_original_A22_HC46_selected_native_gates_green=True,
            all_seven_stage_exits=[0]*7, original_requested_axioms=172,
            project_closure_sources=319, cache_objects_unchanged=566,
            independent_vm_status='TERMINATED', bad_profiles=0, missing_objects=0,
            owned_error_headers=0, owned_warning_headers=[0]*7,
            inherited_regression_headers=[0]*7, custody_sha256='pinned',
            full90_expanded_native_gates_green=True, expanded_requested_axiom_count=173,
            added_requested_axioms=[REQUEST], material_export_bad_or_missing_axioms=False,
            fresh_auxiliary_inputs_preserved=True, material_export_axioms=['propext'])

    def test_green_boundary(self):
        require_qualified_green(self.native, self.qualified, 'pinned')

    def test_failed_stage_is_rejected_despite_green_label(self):
        self.qualified['all_seven_stage_exits'][6] = 125
        with self.assertRaises(RuntimeError):
            require_qualified_green(self.native, self.qualified, 'pinned')

    def test_shortened_scope_is_rejected(self):
        for field, value in [('original_requested_axioms', 171), ('project_closure_sources', 318), ('cache_objects_unchanged', 565)]:
            altered = copy.deepcopy(self.qualified); altered[field] = value
            with self.assertRaises(RuntimeError):
                require_qualified_green(self.native, altered, 'pinned')

    def test_warning_debt_regression_is_rejected(self):
        self.qualified['inherited_regression_headers'][4] = 1
        with self.assertRaises(RuntimeError):
            require_qualified_green(self.native, self.qualified, 'pinned')

    def test_foreign_custody_is_rejected(self):
        with self.assertRaises(RuntimeError):
            require_qualified_green(self.native, self.qualified, 'foreign')

    def test_material_export_missing_profile_is_rejected(self):
        self.qualified['material_export_bad_or_missing_axioms'] = True
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_material_export_nonstandard_axiom_is_rejected(self):
        self.qualified['material_export_axioms'] = ['sorryAx']
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_unexpanded_scope_is_rejected(self):
        self.qualified['expanded_requested_axiom_count'] = 172
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_changed_auxiliary_harness_is_rejected(self):
        self.qualified['fresh_auxiliary_inputs_preserved'] = False
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

if __name__ == '__main__':
    unittest.main()
