# Verification evidence

The JSON files here are **sanitized provenance extracts**, not the original
execution records. They retain the result, scope, timing, source hashes,
dependency revisions and relevant tool identities. `raw_record_sha256`
identifies the exact original bytes. Removing machine-specific fields does
not constitute a new verification run.

- `optimized-full.json`: the successful 8 November project verification,
  using Lake-validated caches. It builds the threshold, extensions and complete
  classification through `Solution`; it does not run the external comparator.
- `classification.json`: the successful 349-root classification replay with
  329 exclusions, thirteen core-cover/extension groups and seven terminal
  enumerations; `classification-axioms.txt` retains its eight axiom reports.
- `optimized-comparator.json`: the successful sixteen-claim comparison,
  completed 9 November, including NanoDa and Lean's standalone kernel. Its
  `preceding_raw_record_sha256` equals `raw_record_sha256` in
  `optimized-full.json`. All three extracts have the same source manifest.
- `classification-baseline.json`: the successful original 349-root
  classification replay and physical-endpoint audit. It predates the revised
  route and does not certify its changed sources.

The current records identify the frozen candidate checked before promotion.
Its Lean proof sources and certificate inputs match the publication checkout;
manuscript, documentation and publication records were updated afterward.
The comparator took 10 h 32 min 48 s, excluding a fresh project build. Its GNU
resource report measures the outer driver and does not aggregate all sandboxed
subprocess CPU and memory use. Cache reuse in the preceding builds is distinct
from the fresh external-kernel acceptance.

No complete cold-build wall time, aggregate peak memory or disk requirement
has been measured. For cheaper verification without Lean, run
`make check-code WORKERS=2` and `make check-classification-data WORKERS=2`.
These execute native certificate checks, independent audits and source
regeneration checks, rather than kernel replay.

To check the current publication proof inputs against the comparator record:

```sh
python3 -S scripts/check_publication_sources.py
```

This compares all Lean sources, mathematical data (including text root
ledgers), toolchain and dependency pins, and Lake/comparator configuration.
It rejects missing, changed or additional inputs in that scope. Manuscript,
documentation and verification-script changes are outside the check; a pass
establishes input identity, not a new verification run. Use `--record` to
check another published extract.

Source-manifest keys are repository-relative paths. Tool hashes use executable
names rather than installation paths. The concise comparison output, resource
report and axiom report are retained alongside these extracts. Each record's
scope matters: an older successful run does not certify subsequent proof edits.

Raw records stay under ignored `build/`. To prepare a public extract:

```sh
python3 -S scripts/publish_verification_record.py \
  build/path/to/record.json verification/run.json
python3 -S scripts/test_publication_records.py
```

The extractor omits local paths, process IDs, retry history and redundant
metadata. It preserves source hashes exactly and rejects local absolute paths
in retained fields. Publish only after the producing run has completed its
source-stability check. These records are evidence for reported checks;
they are not inputs to the mathematical proof.
