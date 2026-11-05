"""Inspect the installed sources and tools used by a verification run."""
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import stat
import subprocess
import sys


def dependency_state(root):
    """Require exact pinned Git trees, independently of Git's index/stat cache.

    Ignored build products are permitted. Tracked files must match the pinned
    blobs byte for byte, including symlink targets and executable bits.
    """
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    result = {}
    for package in manifest['packages']:
        name = package['name']
        if package['type'] != 'git':
            raise RuntimeError(f'dependency {name}: expected a pinned Git package')
        path = (root / manifest['packagesDir'] / name).resolve()

        def git(*args):
            return subprocess.check_output(['git', '-C', str(path), *args],
                                           stderr=subprocess.PIPE)

        if Path(os.fsdecode(git('rev-parse', '--show-toplevel')).strip()).resolve() != path:
            raise RuntimeError(f'dependency {name}: not its own Git checkout')
        revision = git('rev-parse', 'HEAD').decode().strip()
        if revision != package['rev']:
            raise RuntimeError(f'dependency {name}: HEAD {revision} differs from pin {package["rev"]}')
        status = git('status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')
        if status:
            raise RuntimeError(f'dependency {name}: dirty source tree\n{os.fsdecode(status)}')
        algorithm = git('rev-parse', '--show-object-format').decode().strip()
        entries = {}
        for entry in git('ls-tree', '-rz', '--full-tree', revision).split(b'\0'):
            if not entry:
                continue
            header, filename = entry.split(b'\t', 1)
            mode, kind, oid = header.decode().split()
            relative = os.fsdecode(filename)
            source = path / relative
            if kind != 'blob' or mode not in ('100644', '100755', '120000'):
                raise RuntimeError(f'dependency {name}: unsupported tree entry {relative}')
            actual_mode = source.lstat().st_mode
            if mode == '120000' and stat.S_ISLNK(actual_mode):
                data = os.fsencode(os.readlink(source))
            elif mode != '120000' and stat.S_ISREG(actual_mode):
                if bool(actual_mode & stat.S_IXUSR) != (mode == '100755'):
                    raise RuntimeError(f'dependency {name}: changed executable bit: {relative}')
                data = source.read_bytes()
            else:
                raise RuntimeError(f'dependency {name}: changed file type: {relative}')
            blob = b'blob ' + str(len(data)).encode() + b'\0' + data
            if hashlib.new(algorithm, blob).hexdigest() != oid:
                raise RuntimeError(f'dependency {name}: modified source: {relative}')
            entries[relative] = [mode, hashlib.sha256(data).hexdigest()]
        if git('rev-parse', 'HEAD').decode().strip() != revision:
            raise RuntimeError(f'dependency {name}: HEAD changed during inspection')
        result[name] = {
            'revision': revision, 'git_tree': git('rev-parse', 'HEAD^{tree}').decode().strip(),
            'source_files': len(entries),
            'source_sha256': hashlib.sha256(json.dumps(entries, sort_keys=True).encode()).hexdigest(),
            'status': 'clean; tracked bytes and modes match pinned Git tree',
        }
    return result


def environment_state(root, env, workers):
    def run(command):
        return subprocess.check_output(command, cwd=root, env=env, text=True,
                                       stderr=subprocess.STDOUT).strip()

    settings = json.loads(run(['make', '--no-print-directory', 'verification-config',
                               f'WORKERS={workers}']))
    python = json.loads(run(shlex.split(settings['PYTHON']) + ['-S', '-c',
        'import json,sys; print(json.dumps(dict(version=sys.version, '
        'executable=sys.executable, assertions_enabled=__debug__)))']))
    if not python['assertions_enabled']:
        raise RuntimeError('verification requires Python assertions; remove -O/PYTHONOPTIMIZE')
    return {
        'platform': platform.platform(), 'machine': platform.machine(),
        'logical_cpus': os.cpu_count(),
        'driver_python': {'executable': sys.executable, 'version': sys.version},
        'audit_python': python, 'build_settings': settings,
        'lean': run(['lake', 'env', 'lean', '--version']),
        'lake': run(['lake', '--version']),
        'make': run(['make', '--version']),
        'cxx': run(shlex.split(settings['CXX']) + ['--version']),
        'replay_threads_per_worker': 1,
    }
