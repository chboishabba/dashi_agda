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


## What is actually being parsed?

There are three distinct stages and they must not be conflated:

```text
ERIC export records
    -> ERIC metadata/title/abstract parsing + dedup
    -> authoritative screening decisions
    -> verified retained full-text bytes
    -> scholarly text materialisation
    -> actual full-text scholarly parsing
```

The generic SLR `run_digital_esd_l1_l3.py` owns the first path through verified
full text.

The dashi-side wrapper:

`interop_scripts/digital_esd/run_verified_fulltext_parse.py`

owns only the application glue from the verified P0-G full-text index into the
generic SLR scholarly parser.

It preserves two revisions:

```text
raw PDF/DOCX/HTML bytes
    artifact-sha256:<digest>
        ↓ text extraction
materialised UTF-8 text
    materialized-text-sha256:<digest>
        ↓ generic SLR scholarly parser
candidate document nodes + study facets
```

This prevents line/text anchors from being falsely attributed to the original
binary PDF revision.

### Run L1 -> L3

```bash
python3 interop_scripts/digital_esd/run_l1_l3.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric \
  --decision-overlay /path/to/completed-reviewed-decisions.jsonl \
  --retrieved-manifest /path/to/retrieved-fulltext-manifest.jsonl
```

### Parse the actual verified paper text

```bash
python3 interop_scripts/digital_esd/run_verified_fulltext_parse.py \
  --slr-root ../slr \
  --artifact-root artifacts/digital-esd/real-eric
```

The wrapper:

1. reads only `status=verified` rows from the P0-G full-text index;
2. re-verifies the original artifact digest;
3. materialises UTF-8 text from TXT/HTML/PDF/DOCX;
4. hashes that text as a new parser revision;
5. delegates to SLR's generic
   `interop_scripts/digital_esd/scholarly_fulltext.py run`;
6. emits explicit SLR handoff and parse receipts;
7. reruns the generic fail-closed study-processing census.

PDF extraction requires either `pypdf` or PyMuPDF (`fitz`). DOCX extraction
requires `python-docx`. Unsupported formats fail closed.

The resulting count distinctions remain:

```text
verified full text
    != handed to SLR
    != successfully parsed by SLR
    != reviewed canonical evidence
    != SourceAuditAdmission
```
