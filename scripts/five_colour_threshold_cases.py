#!/usr/bin/env python3
"""Generate the complete 357-case partition for the five-colour threshold."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
from five_colour_distinct_cases import generate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='q5-cases-') as directory:
        repeated = Path(directory) / 'repeated.txt'
        subprocess.run([sys.executable, str(Path(__file__).with_name('five_colour_cases.py')),
                        '--multiplicity', '2', '3', '4', '5', '6', '7',
                        '--output', str(repeated)], check=True, capture_output=True)
        rows = repeated.read_text().splitlines()[1:]
    assert len(rows) == 244
    distinct, _ = generate(15)
    rows += distinct
    assert len(rows) == 357
    Path(args.output).write_text('357\n' + '\n'.join(rows) + '\n')
    print('357 cases: 244 with repeats and 113 distinct')


if __name__ == '__main__':
    main()
