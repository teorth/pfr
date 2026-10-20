import tempfile
import types
import unittest
from pathlib import Path
from unittest.mock import patch
from invoke import Context
import tasks


class DevTests(unittest.TestCase):
    def test_rebuild_refreshes_published_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bp_dir = root / "blueprint"
            (bp_dir / "web").mkdir(parents=True)
            (bp_dir / "print").mkdir()
            (root / "docs" / "blueprint").mkdir(parents=True)
            (root / "docs" / "blueprint" / "obsolete.html").write_text("old")
            def build_pdf(ctx):
                (bp_dir / "print" / "print.pdf").write_bytes(b"new pdf")
            def build_web(ctx):
                (bp_dir / "web" / "index.html").write_text("new web")
            def run_process(path, **kwargs):
                kwargs["callback"]({("modified", "web.tex")})
            watchfiles = types.SimpleNamespace(run_process=run_process,
                                               DefaultFilter=lambda **kwargs: None)
            with patch.dict("sys.modules", watchfiles=watchfiles), \
                 patch.object(tasks, "ROOT", root), patch.object(tasks, "BP_DIR", bp_dir), \
                 patch.object(tasks, "bp", build_pdf), patch.object(tasks, "web", build_web):
                tasks.dev.body(Context())
            self.assertEqual((root / "docs/blueprint/index.html").read_text(), "new web")
            self.assertEqual((root / "docs/blueprint.pdf").read_bytes(), b"new pdf")
            self.assertFalse((root / "docs/blueprint/obsolete.html").exists())
