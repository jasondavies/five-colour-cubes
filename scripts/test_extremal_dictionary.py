"""Ensure the independent audit checks the advertised classification, not a private list."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class DictionaryTests(unittest.TestCase):
    def test_changed_representatives_and_counts_are_rejected(self):
        for field, value in [('repeated_colours', [2, 2]), ('multiplicities', [5, 4, 5])]:
            with self.subTest(field=field), tempfile.TemporaryDirectory(prefix='q5-dictionary-') as temp:
                root = Path(temp)
                (root / 'data').mkdir()
                shutil.copyfile(ROOT / 'data/five-colour-geometry.txt', root / 'data/five-colour-geometry.txt')
                dictionary = json.loads((ROOT / 'data/five-colour-extremal.json').read_text())
                dictionary['classes'][0][field] = value
                (root / 'data/five-colour-extremal.json').write_text(json.dumps(dictionary))
                result = subprocess.run([sys.executable, '-S', str(ROOT / 'scripts/check_five_colour_extremal.py'),
                    '--repo', str(root), '--output', str(root / 'report.json')], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('ValueError:', result.stderr)
                self.assertFalse((root / 'report.json').exists())


if __name__ == '__main__':
    unittest.main()
