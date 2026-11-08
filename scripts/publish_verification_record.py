#!/usr/bin/env python3
"""Extract portable provenance from a raw verification record.

Raw records stay in ignored build/. Publication does not rerun verification.
The source manifest is retained exactly; the extract has its own identity and
records the original byte checksum. Unknown fields are omitted deliberately.
"""
import argparse
import hashlib
import json
from pathlib import Path

FIELDS = (
    'status', 'scope', 'started_utc', 'finished_utc', 'cache_policy',
    'external_comparator', 'workers', 'build_threads', 'total', 'passed', 'failed',
    'elapsed_seconds', 'seconds', 'exit_code', 'steps', 'theorem_names',
    'source_sha256', 'source_snapshot_sha256', 'deleted_tracked_files',
    'dependencies', 'source_dependency_tool_stability', 'log_sha256',
    'cpp_executable_sha256',
)


def portable(value):
    """Reject local absolute paths in retained values and dictionary keys."""
    if isinstance(value, dict):
        for key, item in value.items():
            portable(key)
            portable(item)
    elif isinstance(value, list):
        for item in value:
            portable(item)
    elif isinstance(value, str):
        import re
        if re.search(r'(?:^|[\s=\"\'])(?:/(?!/)|[A-Za-z]:[\\/])', value):
            raise ValueError('local absolute path in retained publication field')


def extract(raw):
    data = json.loads(raw)
    if data.get('status') != 'passed':
        raise ValueError('only completed successful verification records may be published')
    result = {
        'format': 'five-colour-verification-extract-v1',
        'record_kind': 'Sanitized provenance extract; not the original execution record.',
        'raw_record_sha256': hashlib.sha256(raw).hexdigest(),
        **{key: data[key] for key in FIELDS if key in data},
    }
    env = data.get('environment', {})
    result['environment'] = {key: env[key] for key in (
        'platform', 'machine', 'logical_cpus', 'build_settings', 'lean', 'lake',
        'replay_threads_per_worker') if key in env}
    if 'audit_python' in env:
        result['environment']['python'] = {
            key: env['audit_python'][key] for key in ('version', 'assertions_enabled')
            if key in env['audit_python']}
    for key in ('make', 'cxx'):
        if key in env:
            result['environment'][key] = env[key].splitlines()[0].split('\\n')[0]
    if 'tool_sha256' in data:
        tools = {Path(key).name: value for key, value in data['tool_sha256'].items()}
        if len(tools) != len(data['tool_sha256']):
            raise ValueError('ambiguous tool basenames')
        result['tool_sha256'] = tools
    if 'verification_record_sha256' in data:
        result['preceding_raw_record_sha256'] = data['verification_record_sha256']
    if 'dependencies_after' in data:
        result['dependency_stability'] = 'passed' if data['dependencies'] == data['dependencies_after'] else 'failed'
    if 'environment_after' in data:
        result['environment_stability'] = 'passed' if env == data['environment_after'] else 'failed'
    if 'generated_sha256' in data:
        if any(data['source_sha256'].get(k) != v for k,v in data['generated_sha256'].items()):
            raise ValueError('generated-file hashes differ from source manifest')
        result['generated_sources'] = 'Hashes are included in source_sha256.'
    portable(result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('raw', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    if args.raw.resolve() == args.output.resolve():
        parser.error('preserve the raw original; choose a different output path')
    args.output.write_text(json.dumps(extract(args.raw.read_bytes()), indent=2)+'\n')


if __name__ == '__main__':
    main()
