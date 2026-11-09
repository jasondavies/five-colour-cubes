#!/usr/bin/env python3
"""Publication identity checks reject drift while allowing editorial changes."""
import hashlib
import tempfile
import unittest
from pathlib import Path
from check_publication_sources import check_sources, source_names


class PublicationSources(unittest.TestCase):
    def test_drift_and_editorial_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            contents = {'Proof.lean': 'proof', 'data/root.txt': 'root',
                        'lean-toolchain': 'pin', 'README.md': 'old prose'}
            for name, value in contents.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(value)
            record = {'status': 'passed', 'source_sha256': {
                name: hashlib.sha256(value.encode()).hexdigest()
                for name, value in contents.items()}}
            def check():
                return check_sources(root, record, source_names(root))
            self.assertEqual(check(), (3, []))
            (root / 'README.md').write_text('new prose')
            self.assertEqual(check(), (3, []))
            (root / 'data/root.txt').write_text('changed root')
            self.assertEqual(check()[1], ['changed: data/root.txt'])
            (root / 'data/root.txt').unlink()
            self.assertEqual(check()[1], ['missing: data/root.txt'])
            (root / 'Extra.lean').write_text('extra')
            self.assertIn('unrecorded: Extra.lean', check()[1])
            record['status'] = 'running'
            with self.assertRaises(ValueError):
                check()


if __name__ == '__main__':
    unittest.main()
