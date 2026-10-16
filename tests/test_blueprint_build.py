import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from invoke import Context
from blueprint import tasks


class BuildDirectoryTests(unittest.TestCase):
    def test_directory_restored_on_success_and_failure(self):
        original = Path.cwd()
        for name in ("print_bp", "bp", "bptt", "web"):
            for fail in (False, True):
                with self.subTest(task=name, fail=fail), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp).resolve()
                    (root / "src").mkdir()
                    observed = []
                    def run(command):
                        observed.append(Path.cwd())
                        if fail:
                            raise RuntimeError("build failed")
                    with patch.object(tasks, "BP_DIR", root), patch.object(tasks, "run", run):
                        if fail:
                            with self.assertRaises(RuntimeError):
                                getattr(tasks, name).body(Context())
                        else:
                            getattr(tasks, name).body(Context())
                    self.assertEqual(Path.cwd(), original)
                    self.assertTrue(observed)
                    self.assertTrue(all(p == (root / "src" if name == "web" else root)
                                        for p in observed))


if __name__ == "__main__":
    unittest.main()
