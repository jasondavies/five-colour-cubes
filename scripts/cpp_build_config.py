#!/usr/bin/env python3
"""Invalidate cached C++ audit tools when their compiler or flags change."""
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

path = Path(sys.argv[1])
compiler = os.environ['VERIFY_CXX']
value = {'compiler': compiler, 'flags': os.environ['VERIFY_CXXFLAGS'],
         'version': subprocess.check_output(shlex.split(compiler) + ['--version'], text=True).strip()}
text = json.dumps(value, sort_keys=True, indent=2) + '\n'
if not path.exists() or path.read_text() != text:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as stream:
        stream.write(text)
        temporary = Path(stream.name)
    temporary.replace(path)
