#!/usr/bin/env python3
"""Create the deterministic archive after a complete certificate-producing run."""
import gzip
import io
import json
from pathlib import Path
import tarfile

OUT=Path(__file__).resolve().parents[1]/'data'
records=json.loads((OUT/'q5-boxes-size15.json').read_text())
assert len(records)==357 and {r['case'] for r in records}==set(range(357))
assert all(r['status']=='UNSAT' for r in records)
rows=[bytes(map(int,r.split())) for r in (OUT/'q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
archive=OUT/'q5-certificates.tar.gz'
with archive.open('wb') as out:
    with gzip.GzipFile(fileobj=out,mode='wb',mtime=0,filename='') as gz:
        with tarfile.open(fileobj=gz,mode='w|') as tar:
            for i,row in enumerate(rows):
                data=(OUT/f'q5-certificates/case-{i}.q5p').read_bytes()
                assert data[:160]==b'Q5P2'+row
                info=tarfile.TarInfo(f'case-{i}.q5p')
                info.size=len(data);info.mode=0o644
                tar.addfile(info,io.BytesIO(data))
print('Archive bytes:',archive.stat().st_size)
