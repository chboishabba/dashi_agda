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


## Run the already-verified full text now

If the SLR-side P0-G/full-text index is already complete, you do **not** need to
rerun ERIC acquisition/screening first.

From `dashi_agda`:

```bash
python3 interop_scripts/digital_esd/run_verified_fulltext_parse.py \
  --slr-root ../slr \
  --artifact-root artifacts/digital-esd/real-eric
```

For a bounded smoke run first:

```bash
python3 interop_scripts/digital_esd/run_verified_fulltext_parse.py \
  --slr-root ../slr \
  --artifact-root artifacts/digital-esd/real-eric \
  --max-items 20
```

Omit `--max-items` to parse every verified artifact in the P0-G index.

The wrapper writes under the SLR artifact root by default:

```text
artifacts/digital-esd/real-eric/slr-parse/
  materialized-text/
  materialization-receipts.jsonl
  scholarly-parser-input.jsonl
  slr-handoff-receipts.jsonl
  parser/
    requests.jsonl
    parser-output.jsonl
    verified.jsonl
  slr-parse-receipts.jsonl
  study_processing_census_with_parse.json
  study-processing-ledger.jsonl
  study-processing-ledger-manifest.json
  fulltext-retrieval-residual.jsonl
  fulltext-retrieval-residual-manifest.json
  verified-fulltext-parse-run.json
```

### One-command replay through L5

If you want to rerun from retained ERIC exports through actual paper parsing:

```bash
python3 interop_scripts/digital_esd/run_l1_l5.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric \
  --decision-overlay /path/to/completed-reviewed-decisions.jsonl \
  --retrieved-manifest /path/to/retrieved-fulltext-manifest.jsonl
```

For a bounded parser smoke pass add:

```text
--parse-max-items 20
```

The L1→L5 wrapper delegates L1→L3 entirely to the generic SLR runtime and then
uses the verified-full-text parse bridge above. It does not copy ERIC parsing,
screening, full-text indexing, or scholarly parsing semantics into dashi_agda.


## Processing denominator and next-retrieval residual

Every verified-full-text parse run now also executes:

`build_processing_ledger.py`

which emits one processing row for every ERIC metadata record. For the current
corpus that means **43,996 processing rows**, even when only a small number of
full-text artifacts exist.

Per source the ledger records observed membership in:

```text
authoritative screening decision
include/probable retained set
verified full text
text materialised
handed to SLR
parsed by SLR
reviewed canonical evidence
SourceAuditAdmission
```

Each later stage is accepted only when its earlier-stage receipt is present.
Later stages are never used to infer missing earlier receipts.

The same run then executes:

`build_fulltext_retrieval_residual.py`

which emits only records that are:

```text
authoritatively include/probable
AND
do not yet have verified full-text bytes
```

Unreviewed metadata-only records are not counted as retrieval failures and do
not enter that queue.

The observed EJ1083370 smoke run therefore means exactly:

```text
metadata denominator              43,996
verified full-text available           1
materialised text                      1
handed to SLR                          1
parsed by SLR                          1
reviewed canonical evidence            0
SourceAuditAdmission                   0
```

That does not imply the other 43,995 records failed parsing; they have not
reached that stage.
