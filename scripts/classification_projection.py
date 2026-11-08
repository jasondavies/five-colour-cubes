"""Checked inputs and Lean adapters for projected fourteen-copy exclusions.

Projection preserves the original anchor and bounds. These certificates prove
empty roots; no terminal census or fifteen-copy threshold justifies exclusion.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
from generate_five_colour_chunks import generate as generate_chunks

ROOT = Path(__file__).resolve().parents[1]


def projected_row(source, retained):
    """Reconstruct the header from the original root, not supplied bounds."""
    if len(source) != 156:
        raise ValueError('invalid original root width')
    anchor, multiplicity, budget = source[4], source[1], source[5]
    if not (0 <= anchor < 75 and 1 <= multiplicity <= 5
            and 0 <= retained <= budget
            and source[6+anchor] == source[81+anchor] == 0
            and all(v in (0, 1) for v in source[81:])):
        raise ValueError('invalid projection conditions')
    row = source[:]
    row[3], row[5] = 14-budget+retained, retained
    if row[3] < multiplicity:
        raise ValueError('projection cannot preserve anchor')
    for i in range(75):
        if source[81+i]:
            row[6+i] = min(source[6+i], retained)
    return row


def load_projections(originals, work):
    metadata = json.loads((ROOT/'data/five-colour-classification-projections.json').read_text())
    archive_path = ROOT/'data/five-colour-classification-projections.tar.gz'
    if (metadata['format'] != 1 or metadata['original_total'] != 14
            or hashlib.sha256(archive_path.read_bytes()).hexdigest() != metadata['archive_sha256']):
        raise ValueError('invalid projection archive identity')
    entries = metadata['cases']
    if ([c['index'] for c in entries] != list(range(137))
            or len({c['original_root'] for c in entries}) != len(entries)):
        raise ValueError('invalid projection case mapping')
    result, rows = {}, []
    with tarfile.open(archive_path) as archive:
        members = archive.getmembers()
        expected = {f'case-{i}.q5p' for i in range(len(entries))}
        if len(members) != len(expected) or {m.name for m in members} != expected or any(not m.isfile() for m in members):
            raise ValueError('invalid projection archive members')
        for entry in entries:
            r, i = entry['original_root'], entry['index']
            if not 0 <= r < len(originals):
                raise ValueError('invalid original root index')
            row = projected_row(originals[r], entry['retained_budget'])
            payload = archive.extractfile(f'case-{i}.q5p').read()
            if (payload[:160] != b'Q5P2'+bytes(row) or row[3] != entry['goal']
                    or len(payload) != entry['certificate_bytes']
                    or hashlib.sha256(payload).hexdigest() != entry['certificate_sha256']):
                raise ValueError(f'projection certificate/header mismatch: {r}')
            path = work/f'projection-{i}.q5p'
            path.write_bytes(payload)
            result[r] = (entry, row, path)
            rows.append(row)
    cases = work/'projection-cases.txt'
    cases.write_text(str(len(rows))+'\n'+'\n'.join(' '.join(map(str,r)) for r in rows)+'\n')
    return result, cases


def generate_projected_case(case, entry, row, certificate, cases, work, dest):
    tsv = work/f'projection-{case}.tsv'
    subprocess.run([str(ROOT/'build/five_colour_chunks'), str(ROOT/'data/five-colour-geometry.txt'),
                    str(cases), str(certificate), str(entry['index']), '128', str(tsv)],
                   check=True, stdout=subprocess.DEVNULL)
    stats = generate_chunks(case, row, tsv, 128, dest, 'EnumerationChunks', 'auto')
    if stats['commands'] != entry['new_instructions']:
        raise ValueError('projection instruction count mismatch')
    return {'case':case, 'original_root':entry['original_root'], 'commands':stats['commands'],
            'chunks':stats['chunks'], 'points':0, 'route':'projection',
            'projected_total':row[3], 'retained_budget':row[5], 'cut_mode':stats['cut_mode']}
