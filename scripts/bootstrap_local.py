#!/usr/bin/env python3
"""Prepare ignored dependencies from a sibling checkout, checking fixed revisions.

The remote Lake manifest is unchanged. This is a local development convenience
until the pinned core revision is available to an ordinary fresh clone.
"""
import argparse,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def git(path,*args):
 return subprocess.check_output(['git','-C',str(path),*args],text=True).strip()
def materialize(dest):
 # Retain the source cache unchanged. Reflinks avoid extra space where supported;
 # ordinary copies are safe too, unlike hard links to mutable Lake outputs.
 source=dest.resolve()
 with tempfile.TemporaryDirectory(prefix=f'.{dest.name}-copy-',dir=dest.parent) as temp:
  staged=Path(temp)/dest.name
  subprocess.run(['cp','-a','--reflink=auto',str(source),str(staged)],check=True)
  dest.unlink() # remove only the original symlink, never its target
  staged.rename(dest)
 print(f'Materialized {dest.name} for the comparator sandbox.')
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--materialize',action='store_true',help='copy cached dependencies inside this checkout for comparator sandboxing')
 p.add_argument('--from-checkout',type=Path,default=ROOT.parent/'colour-cubes-core')
 a=p.parse_args();source=a.from_checkout.resolve()
 packages=ROOT/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
 for dep in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
  name=dep['name'];dest=packages/name
  if dest.exists():
   if git(dest,'rev-parse','HEAD')!=dep['rev']:raise SystemExit(f'Wrong existing revision: {dest}')
   if a.materialize and dest.is_symlink():materialize(dest)
   continue
  origin=source if name=='colour_cubes_core' else source/'.lake/packages'/name
  if not origin.exists():raise SystemExit(f'Missing cached dependency: {origin}')
  if name=='colour_cubes_core':
   subprocess.run(['git','clone','--quiet','--no-hardlinks',str(origin),str(dest)],check=True)
   subprocess.run(['git','-C',str(dest),'checkout','--quiet','--detach',dep['rev']],check=True)
   subprocess.run(['git','-C',str(dest),'remote','set-url','origin',dep['url']],check=True)
  else:
   if git(origin,'rev-parse','HEAD')!=dep['rev']:raise SystemExit(f'Cached revision mismatch: {origin}')
   subprocess.run(['git','-C',str(origin),'diff','--quiet','HEAD'],check=True)
   dest.symlink_to(origin.resolve(),target_is_directory=True)
   if a.materialize:materialize(dest)
 print('Pinned local dependencies prepared; remote manifest unchanged.')
if __name__=='__main__':main()
