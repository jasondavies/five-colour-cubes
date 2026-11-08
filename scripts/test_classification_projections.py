#!/usr/bin/env python3
"""Projection-boundary regressions: preserve anchor, total, and budget caps."""
import unittest
from unittest.mock import patch
import json
from pathlib import Path
import shutil
import tempfile
from classification_projection import load_projections
from classification_projection import ROOT, projected_row


class ProjectionControls(unittest.TestCase):
    def setUp(self):
        self.rows = [list(map(int,l.split())) for l in
                     (ROOT/'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]

    def test_preserves_original_anchor_and_unbudgeted_bounds(self):
        source = self.rows[41]
        for retained in range(source[5]+1):
            row = projected_row(source, retained)
            self.assertEqual(row[3], 14-source[5]+retained)
            self.assertEqual(row[4], source[4])
            self.assertEqual(row[1], source[1])
            self.assertEqual(row[81:], source[81:])
            for i in range(75):
                self.assertEqual(row[6+i], min(source[6+i],retained)
                                 if source[81+i] else source[6+i])
        self.assertEqual(self.rows[41], source)

    def test_invalid_budget_and_anchor_rejected(self):
        source = self.rows[41]
        for retained in (-1, source[5]+1):
            with self.assertRaises(ValueError):
                projected_row(source, retained)
        for offset in (6, 81):
            bad = source[:]
            bad[offset+source[4]] = 1
            with self.assertRaises(ValueError):
                projected_row(bad, 0)
        bad = source[:]
        bad[5] = 14
        with self.assertRaisesRegex(ValueError, 'preserve anchor'):
            projected_row(bad, 0)

    def test_mapping_and_archive_identity_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'data').mkdir()
            (root/'work').mkdir()
            name = 'five-colour-classification-projections'
            shutil.copyfile(ROOT/f'data/{name}.tar.gz', root/f'data/{name}.tar.gz')
            original = json.loads((ROOT/f'data/{name}.json').read_text())
            for kind in ('budget', 'original', 'duplicate', 'hash'):
                data = json.loads(json.dumps(original))
                if kind == 'budget':
                    data['cases'][0]['retained_budget'] = 1
                elif kind == 'original':
                    data['cases'][0]['original_root'] = -1
                elif kind == 'duplicate':
                    data['cases'][0]['original_root'] = data['cases'][1]['original_root']
                else:
                    data['archive_sha256'] = '0'*64
                (root/f'data/{name}.json').write_text(json.dumps(data))
                with self.subTest(kind=kind), patch('classification_projection.ROOT', root):
                    with self.assertRaises(ValueError):
                        load_projections(self.rows, root/'work')


if __name__ == '__main__':
    unittest.main()
