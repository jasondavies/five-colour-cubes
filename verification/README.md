# Verification evidence

The JSON files here are **sanitized provenance extracts**, not the original
execution records. They retain the result, scope, timing, source hashes,
dependency revisions and relevant tool identities. `raw_record_sha256`
identifies the exact original bytes. Removing machine-specific fields does
not constitute a new verification run.

- `optimized-full.json`: the successful 8 November threshold and extension
  verification on the revised projection sources, using Lake-validated caches.
  It does not run the external comparator or the complete classification.
- `optimized-comparator.json`: the successful fifteen-claim comparison,
  including NanoDa and Lean's standalone kernel. Its
  `preceding_raw_record_sha256` identifies the raw full-verification record;
  it equals `raw_record_sha256` in `optimized-full.json`.
- `classification.json`: the successful revised 349-root classification,
  including all 342 exclusions, seven terminal enumerations and the physical
  endpoint audit; `classification-axioms.txt` retains the six axiom reports.
  This is separate from the fifteen-claim external comparison.
- `classification-baseline.json`: the successful original 349-root
  classification replay and physical-endpoint audit. It predates the revised
  342-exclusion route and does not certify its changed sources.

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
