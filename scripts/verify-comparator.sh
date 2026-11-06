#!/usr/bin/env bash
set -euo pipefail

# Palomar's mandatory local comparison: Lean's kernel and NanoDa.
# --lower-bound checks only the exposed-face rule and the explicit obstruction.
# --universal checks only the universal minimum and explicit collection.
# The default checks all targets in comparator.json.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
mode=full
if [[ "${1:-}" == --lower-bound && $# == 1 ]]; then
  mode=lower-bound
elif [[ "${1:-}" == --universal && $# == 1 ]]; then
  mode=universal
elif [[ $# != 0 ]]; then
  echo "usage: $0 [--lower-bound|--universal]" >&2
  exit 2
fi
for tool in bwrap lake lean python3; do
  command -v "$tool" >/dev/null || { echo "error: missing $tool" >&2; exit 2; }
done
prefix=$(lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin; do
  [[ -x "$prefix/bin/$tool" ]] || { echo "error: toolchain lacks $tool" >&2; exit 2; }
done
if [[ "$mode" == full && ! -f FiveColour/ProjectedChunks/Threshold.lean ]]; then
  echo "error: complete archive replay and final assembly are required first (make replay-data; make replay)" >&2
  exit 2
fi
config=$(mktemp "${TMPDIR:-/tmp}/five-colour-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - "$config" "$prefix" "$mode" <<'PYCONFIG'
import json, pathlib, sys
out, prefix, mode = sys.argv[1:]
config = json.loads(pathlib.Path('comparator.json').read_text())
if mode == 'lower-bound':
    config['solution_module'] = 'FiveColour.ComparatorBridge'
    config['theorem_names'] = ['ColourCubes.exposed_face_rule', 'FiveColour.Puzzle.lower_bound']
elif mode == 'universal':
    config['solution_module'] = 'FiveColour.SubmissionBridge'
    config['theorem_names'] = ['FiveColour.Submission.universal_collection', 'FiveColour.Submission.universal_minimum']
# Keep machine-specific kernel paths out of the submitted configuration.
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
}
pathlib.Path(out).write_text(json.dumps(config, indent=2) + '\n')
PYCONFIG
lake comparator --config "$config"
if [[ "$mode" == lower-bound ]]; then
  echo "Lower-bound comparator passed (2 targets); upper bound and sharp threshold NOT checked."
elif [[ "$mode" == universal ]]; then
  echo "Universal-collection comparator passed (2 targets); the other 13 claims NOT checked."
else
  echo "Full comparator passed (all configured targets; Lean and NanoDa)."
fi
