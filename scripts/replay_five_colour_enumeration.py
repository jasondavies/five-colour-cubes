#!/usr/bin/env python3
"""Bounded-concurrency Lean replay of the 349 classification roots.

Lake validates cached dependencies. The --roots-only option is for staged
integration; it does not claim the physical classification or its axiom audit.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import time
from verification_state import dependency_state, environment_state
from verify_full import source_state
ROOT=Path(__file__).resolve().parents[1]

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--workers',type=int,default=2);p.add_argument('--roots-only',action='store_true');p.add_argument('--cases',nargs='+',type=int);p.add_argument('--wait',action='store_true',help='wait for an active replay before validating the cached result');args=p.parse_args()
 if args.workers<1:p.error('workers must be positive')
 os.environ['LEAN_NUM_THREADS']='1'
 rows=json.loads((ROOT/'FiveColour/EnumerationChunks/manifest.json').read_text())['cases']
 if [r['case'] for r in rows]!=list(range(349)):raise SystemExit('incomplete root manifest')
 selected=list(range(349)) if args.cases is None else args.cases
 if len(set(selected))!=len(selected) or any(i not in range(349) for i in selected):p.error('invalid cases')
 logs=ROOT/'build/classification-replay';logs.mkdir(exist_ok=True,parents=True)
 lock=(logs/'run.lock').open('w')
 try:fcntl.flock(lock,fcntl.LOCK_EX|(0 if args.wait else fcntl.LOCK_NB))
 except BlockingIOError:p.error('another enumeration replay owns this log directory')
 if (logs/'STOP').exists():p.error('remove build/classification-replay/STOP to resume')
 full = not args.roots_only and args.cases is None
 if full:
  inputs,deleted=source_state();dependencies=dependency_state(ROOT)
  environment=environment_state(ROOT,dict(os.environ),args.workers)
  record={'status':'running','source_sha256':inputs,'deleted_tracked_files':deleted,'dependencies':dependencies,'environment':environment,'external_comparator':'not run'}
  (logs/'record.json').write_text(json.dumps(record,indent=2)+'\n')
 subprocess.run(['lake','build','FiveColour.EnumerationRoot'],cwd=ROOT,check=True)
 done={};started=time.monotonic()
 def save(status):
  record={'status':status,'workers':args.workers,'elapsed_seconds':time.monotonic()-started,'total':len(selected),'passed':sum(r['exit_code']==0 for r in done.values()),'failed':sum(r['exit_code']!=0 for r in done.values()),'results':sorted(done.values(),key=lambda r:r['case'])}
  path=logs/'progress.tmp';path.write_text(json.dumps(record,indent=2)+'\n');path.replace(logs/'progress.json')
  if full and status != 'running roots':
   bound=json.loads((logs/'record.json').read_text())
   bound.update(stage=status,elapsed_seconds=round(time.monotonic()-started,2))
   if status.startswith('failed') or status.startswith('sources or'):bound['status']='failed'
   (logs/'record.json').write_text(json.dumps(bound,indent=2)+'\n')
 def replay(i):
  start=time.monotonic()
  if (logs/'STOP').exists():return {'case':i,'exit_code':125,'seconds':0}
  with (logs/f'case-{i}.log').open('w') as out:
   child=subprocess.Popen(['lake','build',f'FiveColour.EnumerationChunks.Case{i}'],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
   while child.poll() is None:
    if (logs/'STOP').exists():
     try:os.killpg(child.pid,signal.SIGTERM)
     except ProcessLookupError:pass
     try:child.wait(timeout=10)
     except subprocess.TimeoutExpired:
      os.killpg(child.pid,signal.SIGKILL);child.wait()
     break
    try:child.wait(timeout=1)
    except subprocess.TimeoutExpired:pass
  return {'case':i,'exit_code':child.returncode,'seconds':round(time.monotonic()-start,2),'commands':rows[i]['commands']}
 save('running roots')
 with ThreadPoolExecutor(max_workers=args.workers) as pool:
  futures={pool.submit(replay,i):i for i in sorted(selected,key=lambda i:-rows[i]['commands'])}
  for f in as_completed(futures):
   r=f.result();done[r['case']]=r;save('running roots')
   print(f'{len(done)}/{len(selected)} root {r["case"]}: {"PASS" if r["exit_code"]==0 else "FAIL"} ({r["seconds"]}s)',flush=True)
 if any(r['exit_code'] for r in done.values()):save('failed roots');raise SystemExit(1)
 if args.roots_only or args.cases is not None:save('selected root proofs passed; physical aggregate not requested');return
 save('building physical classification')
 with (logs/'aggregate.log').open('w') as out:
  r=subprocess.run(['lake','build','FiveColour.ClassificationSubmission'],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 if r.returncode:save('failed physical aggregate');raise SystemExit(1)
 with (logs/'audit.log').open('w') as out:
  r=subprocess.run(['python3','-S','scripts/audit_lean.py','--file','ClassificationAudit.lean'],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 if r.returncode:save('failed classification axiom audit');raise SystemExit(1)
 if (source_state() != (inputs,deleted) or dependency_state(ROOT) != dependencies
     or environment_state(ROOT,dict(os.environ),args.workers) != environment):
  save('sources or dependencies changed during verification');raise SystemExit(1)
 record.update(status='passed',workers=args.workers,elapsed_seconds=round(time.monotonic()-started,2))
 (logs/'record.json').write_text(json.dumps(record,indent=2)+'\n')
 save('physical classification and axiom audit passed')
if __name__=='__main__':main()
