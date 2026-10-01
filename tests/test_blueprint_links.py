import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import tasks
from invoke import Context


class TestBlueprintLinks(unittest.TestCase):
    def test_every_link_is_checked_independent_of_html_formatting(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            declarations = root / '.lake/build/doc/declarations/declaration-data.bmp'
            declarations.parent.mkdir(parents=True)
            declarations.write_text(json.dumps({'declarations': {'Known': {}}}), encoding='utf-8')
            graph = root / 'blueprint/web/dep_graph_document.html'
            graph.parent.mkdir(parents=True)
            graph.write_text(
                '<a class="lean_decl" href="../find/#doc/MissingFirst">Lean</a>'
                '<a class="lean_decl" href="../find/#doc/Known">Lean</a>\n'
                "<a href='../find/#doc/MissingReordered' class='lean_link lean_decl'>Lean</a>\n"
                '<a class="lean_decl"\n href="../find/#doc/MissingMultiline">Lean</a>\n',
                encoding='utf-8')
            output = io.StringIO()
            with patch.object(tasks, 'ROOT', root), patch.object(tasks, 'BP_DIR', root / 'blueprint'), \
                    contextlib.redirect_stdout(output), self.assertRaises(SystemExit) as raised:
                tasks.check.body(Context())
            self.assertEqual(raised.exception.code, 1)
            for declaration in ('MissingFirst', 'MissingReordered', 'MissingMultiline'):
                self.assertIn(declaration, output.getvalue())
