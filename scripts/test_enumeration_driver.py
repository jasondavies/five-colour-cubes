#!/usr/bin/env python3
"""Verification failures must leave terminal records, never a stale running claim."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import replay_five_colour_enumeration as driver


class DriverRecords(unittest.TestCase):
    def run_fixture(self, *, metadata_error=None, process_error=None, worker_error=None,
                    final_sources=None, full=True):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            snapshots = [({'input': 'abc'}, []), final_sources or ({'input': 'abc'}, [])]
            with contextlib.ExitStack() as stack:
                stack.enter_context(patch.object(driver, 'source_state', side_effect=metadata_error or snapshots))
                stack.enter_context(patch.object(driver, 'dependency_state', return_value={'pin': 'test'}))
                stack.enter_context(patch.object(driver, 'environment_state', return_value={'lean': 'test'}))
                calls = stack.enter_context(patch.object(driver.subprocess, 'run', side_effect=process_error))
                stack.enter_context(patch.object(driver, 'replay_case', side_effect=worker_error,
                                                return_value={'case': 0, 'exit_code': 0, 'seconds': 0}))
                stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                code = driver.run_verification(root, root, [{'case': 0, 'commands': 1}], [0], 1, full)
                record = json.loads((root/'record.json').read_text())
                progress = json.loads((root/'progress.json').read_text())
                self.assertIn('finished_utc', record)
                self.assertEqual(record['status'], progress['status'])
                return code, record, calls.call_count

    def test_initial_build_failure(self):
        code, record, calls = self.run_fixture(process_error=subprocess.CalledProcessError(1, ['lake']))
        self.assertEqual(code, 1)
        self.assertEqual(record['status'], 'failed')
        self.assertEqual(record['stage'], 'building enumeration infrastructure')
        self.assertIn('CalledProcessError', record['error'])
        self.assertEqual(calls, 1)

    def test_metadata_failure(self):
        code, record, calls = self.run_fixture(metadata_error=RuntimeError('dirty dependency'))
        self.assertEqual((code, record['status'], calls), (1, 'failed', 0))
        self.assertIn('dirty dependency', record['error'])

    def test_worker_exception(self):
        code, record, calls = self.run_fixture(worker_error=OSError('worker could not start'))
        self.assertEqual((code, record['status'], calls), (1, 'failed', 1))
        self.assertEqual(record['stage'], 'running roots')

    def test_aggregate_and_audit_failures(self):
        for successes, stage in [(1, 'building physical classification'), (2, 'auditing classification axioms')]:
            with self.subTest(stage=stage):
                code, record, _ = self.run_fixture(process_error=[None]*successes + [subprocess.CalledProcessError(1, ['lake'])])
                self.assertEqual((code, record['status'], record['stage']), (1, 'failed', stage))

    def test_changed_sources(self):
        code, record, _ = self.run_fixture(final_sources=({'input': 'changed'}, []))
        self.assertEqual((code, record['status']), (1, 'failed'))
        self.assertIn('changed during verification', record['error'])

    def test_success_and_partial_scope(self):
        code, record, calls = self.run_fixture()
        self.assertEqual((code, record['status'], calls), (0, 'passed', 3))
        code, record, calls = self.run_fixture(full=False)
        self.assertEqual((code, record['status'], calls), (0, 'partial_passed', 1))
        self.assertNotIn('source_sha256', record)

    def test_interrupt(self):
        code, record, _ = self.run_fixture(process_error=KeyboardInterrupt())
        self.assertEqual((code, record['status']), (1, 'interrupted'))


if __name__ == '__main__':
    unittest.main()
