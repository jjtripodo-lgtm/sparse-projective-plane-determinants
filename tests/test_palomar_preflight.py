import json
import tempfile
import unittest
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from palomar_preflight import inspect, physical_lines, toolchain_key


class PreflightTests(unittest.TestCase):
    def make_project(self, root):
        (root / 'LICENSE').write_text('MIT\n')
        p = root / 'companion'
        p.mkdir()
        (p / 'lakefile.toml').write_text('name = "test"\n')
        (p / 'lake-manifest.json').write_text('{}\n')
        (p / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0-rc2\n')
        (p / 'formalization.yaml').write_text('project:\n  name: fixture\n')
        (p / 'Challenge.lean').write_text('module\n\ntheorem verified : True := by sorry\n')
        (p / 'Solution.lean').write_text('module\n\ntheorem verified : True := by trivial\n')
        (p / 'comparator.json').write_text(json.dumps({
            'challenge_module': 'Challenge', 'solution_module': 'Solution',
            'theorem_names': ['verified'], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}))
        return p

    def test_readiness_does_not_claim_verification(self):
        with tempfile.TemporaryDirectory() as t:
            r = Path(t)
            self.make_project(r)
            out = inspect(r)
            self.assertEqual(out['status'], 'STATIC_READY_ONLY')
            self.assertEqual(out['mechanical_verification'], 'NOT_RUN')
            self.assertEqual(out['human_specialist_review'], 'NOT_RUN')

    def test_missing_deprecated_inputs_fail_closed(self):
        with tempfile.TemporaryDirectory() as t:
            r = Path(t)
            p = self.make_project(r)
            (p / 'lean-toolchain').write_text('leanprover/lean4:v4.31.0-rc1\n')
            (p / 'Challenge.lean').unlink()
            (p / 'Sparse.lean').write_text('import Mathlib\n theorem t : True := by trivial\n')
            out = inspect(r)
            self.assertEqual(out['status'], 'BLOCKED')
            self.assertTrue(any('4.31.0' in x for x in out['blockers']))
            self.assertEqual(out['missing_module_headers_count'], 1)
            self.assertTrue(any('source missing' in x for x in out['blockers']))

    def test_unapproved_axiom_and_challenge_size_fail(self):
        with tempfile.TemporaryDirectory() as t:
            r = Path(t)
            p = self.make_project(r)
            cfg = json.loads((p / 'comparator.json').read_text())
            cfg['permitted_axioms'] = ['my_magic_axiom']
            (p / 'comparator.json').write_text(json.dumps(cfg))
            (p / 'Challenge.lean').write_text('module\n' + '-- placeholder\n' * 1001)
            out = inspect(r)
            self.assertEqual(out['status'], 'BLOCKED')
            self.assertTrue(any('permitted_axioms' in x for x in out['blockers']))
            self.assertTrue(any('Challenge exceeds' in x for x in out['blockers']))

    def test_toolchain_order(self):
        self.assertLess(toolchain_key('leanprover/lean4:v4.35.0-rc1'),
                        toolchain_key('leanprover/lean4:v4.35.0-rc2'))
        self.assertGreater(toolchain_key('leanprover/lean4:v4.35.0'),
                           toolchain_key('leanprover/lean4:v4.35.0-rc2'))
        self.assertEqual(physical_lines(b'one\ntwo\n'), 2)
        self.assertEqual(physical_lines(b'one\ntwo'), 2)


if __name__ == '__main__':
    unittest.main()
