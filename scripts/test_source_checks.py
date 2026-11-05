"""Regression checks for missing package modules and read-only replay validation."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from generate_five_colour_chunks import check_sources

ROOT = Path(__file__).resolve().parents[1]


class SourceChecks(unittest.TestCase):
    def test_imported_deletion_is_rejected_before_and_after_staging(self):
        with tempfile.TemporaryDirectory(prefix='q5-package-test-') as temp:
            repo = Path(temp) / 'repo'
            repo.mkdir()
            # Build the fixture from actual sources, including in a Git-free review archive.
            for name in ('FiveColour', 'data'):
                shutil.copytree(ROOT / name, repo / name)
            for name in ('Challenge.lean', 'FiveColour.lean', 'Solution.lean',
                         'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'comparator.json'):
                shutil.copyfile(ROOT / name, repo / name)
            (repo / 'scripts').mkdir()
            shutil.copyfile(ROOT / 'scripts/check_package.py', repo / 'scripts/check_package.py')
            subprocess.run(['git', 'init', '--quiet', str(repo)], check=True)
            subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True)
            command = [sys.executable, '-S', str(repo / 'scripts/check_package.py')]
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            missing = 'FiveColour/ProjectedChunks/Case278.lean'
            (repo / missing).unlink()
            for staged in (False, True):
                if staged:
                    subprocess.run(['git', '-C', str(repo), 'add', '-u', '--', missing], check=True)
                with self.subTest(staged=staged):
                    result = subprocess.run(command, capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn('missing submitted source', result.stderr)
                    self.assertIn('Case278', result.stderr)

    def test_replay_drift_is_reported_without_repairing_sources(self):
        for change in ('modified', 'missing', 'extra', 'modified and extra'):
            with self.subTest(change=change), tempfile.TemporaryDirectory(prefix='q5-replay-test-') as temp:
                generated, retained = Path(temp) / 'generated', Path(temp) / 'retained'
                generated.mkdir(); retained.mkdir()
                (generated / 'Case0.lean').write_text('module\n')
                (retained / 'Case0.lean').write_text('module\n')
                check_sources(generated, retained)
                if change in ('modified', 'modified and extra'):
                    (retained / 'Case0.lean').write_text('module\n-- drift\n')
                elif change == 'missing':
                    (retained / 'Case0.lean').unlink()
                if change in ('extra', 'modified and extra'):
                    (retained / 'Unexpected.lean').write_text('module\n')
                before = {p.name: p.read_bytes() for p in retained.iterdir()}
                with self.assertRaisesRegex(ValueError, 'Retained replay sources differ') as error:
                    check_sources(generated, retained)
                message = str(error.exception)
                if 'extra' in change:
                    self.assertIn('extra: Unexpected.lean', message)
                    self.assertIn('remove the files listed as extra', message)
                if change == 'extra':
                    self.assertNotIn('make replay-data', message)
                else:
                    self.assertIn('make replay-data', message)
                self.assertEqual(before, {p.name: p.read_bytes() for p in retained.iterdir()})


if __name__ == '__main__':
    unittest.main()
