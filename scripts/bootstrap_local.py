#!/usr/bin/env python3
"""Prepare ignored dependencies from a sibling checkout, checking fixed revisions.

The remote Lake manifest is unchanged. This is a local development convenience
until the pinned four-to-three revision is available to an ordinary fresh clone.
"""
import argparse,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def git(path,*args):
 return subprocess.check_output(['git','-C',str(path),*args],text=True).strip()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--from-checkout',type=Path,default=ROOT.parent/'macmahon-four-to-three')
 a=p.parse_args();source=a.from_checkout.resolve()
 packages=ROOT/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
 for dep in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
  name=dep['name'];dest=packages/name
  if dest.exists():
   if git(dest,'rev-parse','HEAD')!=dep['rev']:raise SystemExit(f'Wrong existing revision: {dest}')
   continue
  origin=source if name=='macmahon_four_to_three' else source/'.lake/packages'/name
  if not origin.exists():raise SystemExit(f'Missing cached dependency: {origin}')
  if name=='macmahon_four_to_three':
   subprocess.run(['git','clone','--quiet','--no-hardlinks',str(origin),str(dest)],check=True)
   subprocess.run(['git','-C',str(dest),'checkout','--quiet','--detach',dep['rev']],check=True)
   subprocess.run(['git','-C',str(dest),'remote','set-url','origin',dep['url']],check=True)
  else:
   if git(origin,'rev-parse','HEAD')!=dep['rev']:raise SystemExit(f'Cached revision mismatch: {origin}')
   subprocess.run(['git','-C',str(origin),'diff','--quiet','HEAD'],check=True)
   dest.symlink_to(origin.resolve(),target_is_directory=True)
 print('Pinned local dependencies prepared; remote manifest unchanged.')
if __name__=='__main__':main()
