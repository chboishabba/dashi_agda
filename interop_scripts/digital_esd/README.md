# Digital-ESD interop scripts

This directory contains application-side delegates only.

The generic ERIC parser, screening work-queue runtime, reviewed-decision
application, full-text verifier, SLR handoff, and study-processing census live
in the `slr` repository.

`run_l1_l3.py` delegates to the generic SLR driver and deliberately does not
copy or reimplement those semantics.

Example:

```bash
python3 interop_scripts/digital_esd/run_l1_l3.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric
```

Without a reviewed decision overlay the run parses/deduplicates ERIC metadata,
builds candidate assessments/Pareto work queues, and emits human review packets,
but does not claim any source has been genuinely screened.

To advance authority:

```bash
python3 interop_scripts/digital_esd/run_l1_l3.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric \
  --decision-overlay /path/to/completed-reviewed-decisions.jsonl
```

A retrieved-manifest may then be added to verify include/probable full text.
Later SLR parse/review/SourceAuditAdmission receipts may also be supplied to
the generic census; absent receipts remain zero.
