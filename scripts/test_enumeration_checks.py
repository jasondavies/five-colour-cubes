#!/usr/bin/env python3
"""Focused rejection controls for the independent enumeration replayer."""
from collections import Counter
import copy
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from generate_five_colour_enumeration import reduced_families

ROOT = Path(__file__).resolve().parents[1]

class EnumerationControls(unittest.TestCase):
    def test_dictionary_semantics(self):
        original = json.loads((ROOT/'data/five-colour-classification.json').read_text())
        variants = []
        data = copy.deepcopy(original); data['representatives'][1] = data['representatives'][0]; variants.append(data)
        data = copy.deepcopy(original); data['representatives'][0]['hall_masks'][0] = 0; variants.append(data)
        data = copy.deepcopy(original); data['representatives'][0]['orbit_size'] += 1; variants.append(data)
        data = copy.deepcopy(original); data['representatives'][0]['form'] = 'exceptional'; variants.append(data)
        data = copy.deepcopy(original); data['terminals'][0] = [0]*14; variants.append(data)
        with tempfile.TemporaryDirectory(prefix='q5-classification-controls-') as temp:
            path = Path(temp)/'dictionary.json'
            for i, data in enumerate(variants):
                with self.subTest(corruption=i):
                    path.write_text(json.dumps(data))
                    result = subprocess.run([sys.executable, '-S', str(ROOT/'scripts/check_five_colour_classification.py'),
                                             '--dictionary', str(path)], capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)

    def test_certificate_and_terminal_corruption(self):
        info = json.loads((ROOT/'data/five-colour-classification.json').read_text())
        entry = info['roots'][320]
        originals = (ROOT/'data/q5-threshold-cases-size15.txt').read_text().splitlines()[1:]
        row = list(map(int, originals[entry['original_root']].split()))
        row[3] = 14
        geom = ROOT/'data/five-colour-geometry.txt'
        masks = [list(map(int, l.split())) for l in geom.read_text().splitlines()[76:]]
        families = reduced_families(row, masks)
        points = [[Counter(info['terminals'][j])[i] for i in range(75)] for j in entry['terminals']]
        with tarfile.open(ROOT/'data/five-colour-classification-certificates.tar.gz') as archive:
            payload = archive.extractfile('case-320.q5p').read()
        with tempfile.TemporaryDirectory(prefix='q5-enumeration-controls-') as temp:
            work = Path(temp)
            cases, cert, fs, pts, out = [work/n for n in ['cases', 'cert', 'families', 'points', 'out']]
            cases.write_text('1\n'+' '.join(map(str, row))+'\n')
            fs.write_text('\n'.join(str(len(f))+'\n'+'\n'.join(f'{m&((1<<64)-1)} {m>>64} {r}' for m,r in f) for f in families)+'\n')
            def run(raw, inventories):
                cert.write_bytes(raw)
                pts.write_text(str(len(inventories))+'\n'+'\n'.join(' '.join(map(str,p)) for p in inventories)+'\n')
                return subprocess.run([str(ROOT/'build/five_colour_enumeration'),str(geom),str(cases),str(cert),'0','128',str(out),str(fs),str(pts)],capture_output=True,text=True)
            self.assertEqual(run(payload, points).returncode, 0)
            offset = 160
            while payload[offset] != 3:
                offset += 3 if payload[offset] == 1 else 2
            bad_point = bytearray(payload); bad_point[offset+1] = 1
            bad_header = bytearray(payload); bad_header[7] += 1
            corruptions = [b'BAD!'+payload[4:],payload[:159],payload[:-1],payload+b'\0',
                           payload[:160]+bytes([4,0]),payload[:160]+bytes([0,255]),
                           bytes(bad_point),bytes(bad_header)]
            for raw in corruptions:
                with self.subTest(corruption=corruptions.index(raw)):
                    self.assertNotEqual(run(raw, points).returncode, 0)
            self.assertNotEqual(run(payload, points[1:]).returncode, 0)
            self.assertNotEqual(run(payload, points+[[0]*75]).returncode, 0)

if __name__ == '__main__':
    unittest.main()
