"""Read retained core-cover inputs; no search or mathematical inference."""
import hashlib
import json
from pathlib import Path
import re
import tarfile


def load_core_inputs(root, work):
    data = root / 'data'
    meta = json.loads((data/'five-colour-classification-cores.json').read_text())
    archive = data/'five-colour-classification-cores.tar.gz'
    if (meta['format'] != 1 or meta['original_total'] != 14 or meta['retained_budget'] != 0
            or hashlib.sha256(archive.read_bytes()).hexdigest() != meta['archive_sha256']):
        raise ValueError('invalid core archive identity')
    cases = meta['cases']
    if len({c['original_root'] for c in cases}) != len(cases):
        raise ValueError('duplicate core root')
    expected = set(meta['files'])
    if any(not re.fullmatch(r'r[0-9]+/(search\.json|cover\.q5c|lift-[0-9]+\.q5l)',n) for n in expected):
        raise ValueError('invalid core archive name')
    dest = work/'core-inputs'
    dest.mkdir()
    with tarfile.open(archive) as stream:
        members = stream.getmembers()
        if (len(members) != len(expected) or {m.name for m in members} != expected
                or any(not m.isfile() or m.size > 2_000_000 for m in members)):
            raise ValueError('invalid core archive file set')
        for member in members:
            raw = stream.extractfile(member).read()
            if hashlib.sha256(raw).hexdigest() != meta['files'][member.name]:
                raise ValueError('core input hash mismatch')
            path = dest/member.name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(raw)
    records = {}
    required = set()
    for case in cases:
        r = case['original_root']
        if not 0 <= r < 357:
            raise ValueError('invalid original core root')
        folder = dest/f'r{r}'
        record = json.loads((folder/'search.json').read_text())
        cores = record['cores']
        if (record['original_root'] != r or record['original_total'] != 14
                or record['projected_total'] != case['goal'] or len(cores) != case['cores']
                or not cores or any(len(p) != 75 or any(type(x) is not int or not 0 <= x <= 7 for x in p) for p in cores)
                or len({tuple(p) for p in cores}) != len(cores)):
            raise ValueError('invalid core metadata')
        required |= {f'r{r}/search.json',f'r{r}/cover.q5c'} | {f'r{r}/lift-{i}.q5l' for i in range(len(cores))}
        records[r] = (record, folder)
    if required != expected:
        raise ValueError('extra or missing per-root core inputs')
    return records, dest
