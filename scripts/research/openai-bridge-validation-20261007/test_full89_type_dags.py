import copy
import unittest
from qualify_full89_type_dags import validate_dag


class TypeDagTests(unittest.TestCase):
    def setUp(self):
        self.dag = {'schema': 'lean-expr-type-dag-v1', 'root': 2,
                    'level_nodes': [['zero']],
                    'expr_nodes': [['const', ['str', [], 'Nat'], []],
                                   ['sort', 0], ['app', 0, 1]]}

    def test_shared_valid_dag(self):
        dag = copy.deepcopy(self.dag)
        dag['expr_nodes'].append(['app', 2, 2]); dag['root'] = 3
        self.assertEqual(validate_dag(dag), {'Nat'})

    def test_cycle_rejected(self):
        self.dag['expr_nodes'][2] = ['app', 2, 1]
        with self.assertRaises(ValueError):
            validate_dag(self.dag)

    def test_missing_level_rejected(self):
        self.dag['expr_nodes'][1] = ['sort', 1]
        with self.assertRaises(ValueError):
            validate_dag(self.dag)

    def test_unreachable_nodes_rejected(self):
        self.dag['expr_nodes'].append(['nat', 5])
        with self.assertRaises(ValueError):
            validate_dag(self.dag)

    def test_malformed_constructor_rejected(self):
        self.dag['expr_nodes'][2] = ['app', 0]
        with self.assertRaises(ValueError):
            validate_dag(self.dag)


if __name__ == '__main__':
    unittest.main()
