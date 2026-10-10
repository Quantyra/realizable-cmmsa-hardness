"""Negative qualification-boundary fixtures; not kernel or coverage evidence."""
import copy
import unittest
from full105_consumption_v3_controller import require_qualified_green, ADDITIONAL_REQUESTS

class Gates(unittest.TestCase):
    def setUp(self):
        self.native = dict(compile_green=True)
        self.qualified = dict(full_original_A22_HC46_selected_native_gates_green=True,
            all_seven_stage_exits=[0]*7, original_requested_axioms=172,
            project_closure_sources=344, cache_objects_unchanged=566,
            independent_vm_status='TERMINATED', bad_profiles=0, missing_objects=0,
            owned_error_headers=0, owned_warning_headers=[0]*7,
            inherited_regression_headers=[0]*7, custody_sha256='pinned',
            full105_expanded_native_gates_green=True, expanded_requested_axiom_count=257,
            added_requested_axioms=ADDITIONAL_REQUESTS, material_export_bad_or_missing_axioms=False,
            fresh_auxiliary_inputs_preserved=True, additional_profiles={name:['propext'] for name in ADDITIONAL_REQUESTS})

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
        self.qualified['additional_profiles'][ADDITIONAL_REQUESTS[-1]] = ['sorryAx']
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_unexpanded_scope_is_rejected(self):
        self.qualified['expanded_requested_axiom_count'] = 172
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_changed_auxiliary_harness_is_rejected(self):
        self.qualified['fresh_auxiliary_inputs_preserved'] = False
        with self.assertRaises(RuntimeError): require_qualified_green(self.native, self.qualified, 'pinned')

    def test_missing_added_profile_is_rejected(self):
        self.qualified['additional_profiles'].pop(ADDITIONAL_REQUESTS[-1])
        with self.assertRaises(RuntimeError):
            require_qualified_green(self.native, self.qualified, 'pinned')

    def test_incomplete_warning_scope_is_rejected(self):
        for field in ['owned_warning_headers','inherited_regression_headers']:
            changed=copy.deepcopy(self.qualified)
            changed[field]=changed[field][:-1]
            with self.assertRaises(RuntimeError):
                require_qualified_green(self.native, changed, 'pinned')

    def test_previous_material_scope_is_rejected(self):
        changed=copy.deepcopy(self.qualified)
        changed['expanded_requested_axiom_count']=173
        changed['added_requested_axioms']=ADDITIONAL_REQUESTS[:1]
        with self.assertRaises(RuntimeError):
            require_qualified_green(self.native, changed, 'pinned')

if __name__ == '__main__':
    unittest.main()
