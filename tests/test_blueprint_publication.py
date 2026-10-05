from pathlib import Path
import os
import tempfile
import unittest
from unittest.mock import patch
from invoke import Context
import tasks

class PublicationTests(unittest.TestCase):
    def test_failed_staging_preserves_previous_site(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root)
            def interrupted_copy(source, destination):
                Path(destination).mkdir(parents=True)
                (Path(destination) / 'partial.html').write_text('partial')
                raise OSError('disk full')
            with patch.object(tasks, 'ROOT', root), patch.object(tasks.shutil, 'copytree', side_effect=interrupted_copy):
                with self.assertRaisesRegex(OSError, 'disk full'):
                    tasks.all.body(Context())
            self.assertEqual((root / 'docs/blueprint/index.html').read_text(), 'old html')
            self.assertEqual((root / 'docs/blueprint.pdf').read_text(), 'old pdf')
            self.assertEqual(sorted(p.name for p in (root / 'docs').iterdir()), ['blueprint', 'blueprint.pdf'])

    def test_failed_pdf_replacement_rolls_back_html(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root)
            replace = os.replace
            failed = False
            def fail_once(source, destination):
                nonlocal failed
                if Path(source).name == 'print.pdf' and not failed:
                    failed = True
                    raise OSError('replacement failed')
                return replace(source, destination)
            with patch.object(tasks, 'ROOT', root), patch.object(tasks.os, 'replace', side_effect=fail_once):
                with self.assertRaisesRegex(OSError, 'replacement failed'):
                    tasks.all.body(Context())
            self.assertEqual((root / 'docs/blueprint/index.html').read_text(), 'old html')
            self.assertEqual((root / 'docs/blueprint.pdf').read_text(), 'old pdf')
            self.assertEqual(sorted(p.name for p in (root / 'docs').iterdir()), ['blueprint', 'blueprint.pdf'])

    def test_successful_html_and_pdf_publication(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root)
            with patch.object(tasks, 'ROOT', root):
                tasks.all.body(Context())
            self.assertEqual((root / 'docs/blueprint/index.html').read_text(), 'new html')
            self.assertEqual((root / 'docs/blueprint.pdf').read_text(), 'new pdf')

    def test_html_only_preserves_pdf(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root)
            with patch.object(tasks, 'ROOT', root):
                tasks.html.body(Context())
            self.assertEqual((root / 'docs/blueprint/index.html').read_text(), 'new html')
            self.assertEqual((root / 'docs/blueprint.pdf').read_text(), 'old pdf')

    @staticmethod
    def fixture(root):
        for directory in ['blueprint/web', 'blueprint/print', 'docs/blueprint']:
            (root / directory).mkdir(parents=True)
        for path, content in [('blueprint/web/index.html', 'new html'), ('blueprint/print/print.pdf', 'new pdf'),
                              ('docs/blueprint/index.html', 'old html'), ('docs/blueprint.pdf', 'old pdf')]:
            (root / path).write_text(content)

if __name__ == '__main__':
    unittest.main()
