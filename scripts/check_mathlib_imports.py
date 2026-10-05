"""Check that PFR.Mathlib imports no project modules outside PFR.Mathlib."""

from pathlib import Path
import re
import sys


def check(root):
    invalid = []
    for path in sorted(root.rglob('*.lean')):
        for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
            match = re.match(r'\s*import\s+(.*)', line)
            if match:
                for module in match[1].split('--', 1)[0].split():
                    if (module == 'PFR' or module.startswith('PFR.')) and not (
                        module == 'PFR.Mathlib' or module.startswith('PFR.Mathlib.')
                    ):
                        invalid.append(f'{path}:{number}: forbidden import {module}')
    return invalid


if __name__ == '__main__':
    root = Path(__file__).resolve().parent.parent / 'PFR' / 'Mathlib'
    if not root.is_dir():
        sys.exit(f'Missing source directory: {root}')
    errors = check(root)
    for error in errors:
        print(error)
    sys.exit(bool(errors))
