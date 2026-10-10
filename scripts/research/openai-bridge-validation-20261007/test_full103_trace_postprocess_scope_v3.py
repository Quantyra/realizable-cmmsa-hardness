"""Synthetic scope and failure-boundary checks; never native proof evidence."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class ExpandedScope(unittest.TestCase):
    def run_case(self, roots_count=251, focused_count=83, mutate=None):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            script = folder/'postprocess.py'
            shutil.copyfile(Path(__file__).with_name('full103_trace_postprocess_scope_v3.py'), script)
            roots = ['synthetic.root'+str(i) for i in range(roots_count)]
            spec = dict(roots=roots, focused_roots=roots[:focused_count])
            rows = [dict(name=name, project=True, union_edges=[], type_repr='synthetic') for name in roots]
            if mutate:
                mutate(spec, rows)
            (folder/'preparation-status.json').write_text(json.dumps(spec), encoding='utf-8')
            raw = folder/'raw.jsonl'
            raw.write_text('\n'.join(json.dumps(row) for row in rows)+'\n', encoding='utf-8')
            result = subprocess.run([sys.executable, '-B', '-X', 'utf8', str(script), str(raw), str(folder/'graphs')],
                                    capture_output=True)
            output = folder/'graphs/validated-graphs.json'
            return result.returncode, json.loads(output.read_bytes()) if output.exists() else None

    def test_complete_expanded_scope(self):
        code, value = self.run_case()
        self.assertEqual(code, 0)
        self.assertEqual(len(value['graphs']['exact251-native']['roots']), 251)
        self.assertEqual(len(value['graphs']['focused-eighty-three-consumer']['roots']), 83)
        self.assertFalse(value['mathematical_acceptance'])

    def test_historical_scope_rejected(self):
        self.assertNotEqual(self.run_case(192, 24)[0], 0)

    def test_missing_focused_root_rejected(self):
        self.assertNotEqual(self.run_case(focused_count=82)[0], 0)

    def test_duplicate_root_rejected(self):
        self.assertNotEqual(self.run_case(mutate=lambda spec, rows: spec['roots'].__setitem__(-1, spec['roots'][0]))[0], 0)

    def test_foreign_focused_root_rejected(self):
        self.assertNotEqual(self.run_case(mutate=lambda spec, rows: spec['focused_roots'].__setitem__(-1, 'foreign.root'))[0], 0)

    def test_missing_raw_root_rejected(self):
        self.assertNotEqual(self.run_case(mutate=lambda spec, rows: rows.pop())[0], 0)

    def test_duplicate_raw_node_rejected(self):
        self.assertNotEqual(self.run_case(mutate=lambda spec, rows: rows.append(dict(rows[0])))[0], 0)

    def test_unresolved_body_remains_explicit(self):
        code, value = self.run_case(mutate=lambda spec, rows: rows[0].update(body_unresolved=True))
        self.assertEqual(code, 0)
        for graph in value['graphs'].values():
            self.assertEqual(len(graph['unresolved']), 1)
            self.assertFalse(graph['coverage_accepted'])


if __name__ == '__main__':
    unittest.main()
