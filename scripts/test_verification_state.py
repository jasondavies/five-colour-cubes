"""Regression checks for dependency provenance; all Git mutations use fixtures."""
import json
import os
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from verification_state import dependency_state, make_settings
import verify_full


class DependencyStateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='q5-provenance-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.dep = self.root / '.lake/packages/fixture'
        self.dep.mkdir(parents=True)
        for path in (self.root, self.dep):
            self.git(path, 'init', '--quiet', '--template=')
        (self.root / '.gitignore').write_text('.lake/\nbuild/\nFiveColour/ProjectedChunks/\n')
        (self.dep / '.gitignore').write_text('.lake/\n')
        (self.dep / 'Source.lean').write_text('-- pinned source\n')
        self.git(self.dep, 'add', '.')
        self.git(self.dep, 'commit', '-qm', 'fixture')
        self.revision = self.git(self.dep, 'rev-parse', 'HEAD').strip()
        manifest = {'packagesDir': '.lake/packages', 'packages': [
            {'name': 'fixture', 'type': 'git', 'rev': self.revision}]}
        (self.root / 'lake-manifest.json').write_text(json.dumps(manifest))
        self.git(self.root, 'add', '.')
        self.git(self.root, 'commit', '-qm', 'fixture')

    def git(self, path, *args):
        return subprocess.check_output(['git', '-c', 'user.name=Test', '-c',
            'user.email=test@example.invalid', '-c', 'commit.gpgsign=false',
            '-C', str(path), *args], text=True, stderr=subprocess.PIPE)

    def test_build_cache_is_allowed(self):
        before = dependency_state(self.root)
        (self.dep / '.lake').mkdir()
        (self.dep / '.lake/cached.olean').write_bytes(b'build fixture')
        self.assertEqual(before, dependency_state(self.root))
        self.assertEqual(before['fixture']['revision'], self.revision)
        self.assertEqual(before['fixture']['source_files'], 2)

    def test_wrong_revision_is_rejected(self):
        (self.dep / 'Source.lean').write_text('-- different revision\n')
        self.git(self.dep, 'commit', '-qam', 'different')
        with self.assertRaisesRegex(RuntimeError, 'differs from pin'):
            dependency_state(self.root)

    def test_dirty_tracked_source_is_rejected(self):
        (self.dep / 'Source.lean').write_text('-- changed comment\n')
        with self.assertRaisesRegex(RuntimeError, 'dirty source tree'):
            dependency_state(self.root)

    def test_untracked_source_is_rejected(self):
        (self.dep / 'Extra.lean').write_text('-- extra source\n')
        with self.assertRaisesRegex(RuntimeError, 'dirty source tree'):
            dependency_state(self.root)

    def test_git_assume_unchanged_cannot_hide_modified_bytes(self):
        self.git(self.dep, 'update-index', '--assume-unchanged', 'Source.lean')
        (self.dep / 'Source.lean').write_text('-- changed comment\n')
        self.assertEqual(self.git(self.dep, 'status', '--porcelain'), '')
        with self.assertRaisesRegex(RuntimeError, 'modified source'):
            dependency_state(self.root)

    def test_preflight_failure_is_recorded_before_any_stage(self):
        (self.dep / 'Source.lean').write_text('-- dirty before verification\n')
        with patch.object(verify_full, 'ROOT', self.root), \
             patch.object(sys, 'argv', ['verify_full.py']), redirect_stdout(StringIO()):
            self.assertEqual(verify_full.main(), 1)
        record = json.loads(next((self.root / 'build/verification').glob('*/record.json')).read_text())
        self.assertEqual(record['status'], 'failed')
        self.assertEqual(record['steps'], [])
        self.assertIn('dirty source tree', record['error'])

    def test_change_during_verification_is_rejected(self):
        original_popen = subprocess.Popen

        class Child:
            stdout = ()

            def wait(self):
                return 0

        def stage_or_real(command, **kwargs):
            if command[0] == 'make':
                (self.dep / 'Source.lean').write_text('-- changed during verification\n')
                return Child()
            return original_popen(command, **kwargs)

        with patch.object(verify_full, 'ROOT', self.root), \
             patch.object(verify_full, 'environment_state', return_value={'test': True}), \
             patch.object(subprocess, 'Popen', side_effect=stage_or_real), \
             patch.object(sys, 'argv', ['verify_full.py']), redirect_stdout(StringIO()):
            self.assertEqual(verify_full.main(), 1)
        record = json.loads(next((self.root / 'build/verification').glob('*/record.json')).read_text())
        self.assertEqual(record['status'], 'failed')
        self.assertEqual(len(record['steps']), 5)
        self.assertIn('dirty source tree', record['error'])
        self.assertIn('fixture', record['dependencies'])


class MakeSettingsTests(unittest.TestCase):
    def test_diagnostics_and_command_line_overrides(self):
        root = Path(__file__).resolve().parents[1]
        for flags in ['', '-j2 --jobserver-auth=300,301', '--trace']:
            with self.subTest(flags=flags):
                env = dict(os.environ, MAKEFLAGS=flags + ' -- CXXFLAGS=-DFIXTURE=7')
                settings = make_settings(root, env, 3)
                self.assertEqual(settings['WORKERS'], '3')
                self.assertEqual(settings['CXXFLAGS'], '-DFIXTURE=7')
                self.assertIn('PYTHON', settings)


if __name__ == '__main__':
    unittest.main()
