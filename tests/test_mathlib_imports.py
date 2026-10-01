import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'check_mathlib_imports', Path(__file__).resolve().parents[1] / 'scripts/check_mathlib_imports.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class TestMathlibImports(unittest.TestCase):
    def test_forbidden_project_imports_are_reported_with_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Fixture.lean').write_text(
                'import Mathlib.Data.Nat.Basic\n'
                'import PFR.Mathlib.Data.Nat\n'
                'import PFR.Entropy\n'
                'import PFR.MathlibExtra\n'
                'import PFR\n'
                '-- import PFR.Ignored\n'
                'import Mathlib.Tactic PFR.Other\n', encoding='utf-8')
            errors = checker.check(root)
            self.assertEqual(len(errors), 4)
            for number, module in [(3, 'PFR.Entropy'), (4, 'PFR.MathlibExtra'),
                                   (5, 'PFR'), (7, 'PFR.Other')]:
                self.assertIn(f'{root / "Fixture.lean"}:{number}: forbidden import {module}', errors)
