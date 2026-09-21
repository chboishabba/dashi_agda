# Digital-ESD interop scripts

This directory is the **application-side compatibility boundary** between
Digital-ESD and external SLR/SensibLaw tooling.

It is intentionally not a new semantic subsystem.

## Rule

```text
Digital-ESD application artifacts
        ↓
thin interop wrapper
        ↓
configured external SLR capability
        ↓
canonical SLR receipts
        ↓
same-object reconciliation
        ↓
Digital-ESD may consume the reconciled candidate evidence
```

The wrapper does **not** own document parsing, evidence semantics, review,
reduction, truth, applicability, or `SourceAuditAdmission`.

## CLI

Prepare a stable request from Digital-ESD full-text/canonical evidence output:

```bash
python3 interop_scripts/digital_esd_slr.py prepare \
  --input artifacts/digital-esd/fulltext/canonical-fulltext-evidence.jsonl \
  --output artifacts/digital-esd/slr-interop/requests.jsonl
```

Invoke an external SLR command through a local JSON config:

```bash
python3 interop_scripts/digital_esd_slr.py run \
  --input artifacts/digital-esd/slr-interop/requests.jsonl \
  --config interop_scripts/digital_esd_slr.example.json \
  --output-dir artifacts/digital-esd/slr-interop/run
```

Verify normalized SLR receipts before Digital-ESD consumes them:

```bash
python3 interop_scripts/digital_esd_slr.py verify \
  --input artifacts/digital-esd/slr-interop/requests.jsonl \
  --receipts artifacts/digital-esd/slr-interop/run/canonical-receipts.jsonl \
  --output artifacts/digital-esd/slr-interop/verified-receipt.json
```

## External command contract

The wrapper deliberately does not hard-code the SLR repository layout.
The config contains an argv array and may use `{input}` and `{output_dir}`.

The external tool is responsible for producing a normalized receipt JSONL
containing, at minimum:

```json
{
  "source_identity_reference": "ERIC:EJ123456",
  "source_revision_ref": "fulltext-sha256:...",
  "content_digest_ref": "sha256:...",
  "observation_ref": "observation:...",
  "candidate_only": true,
  "creates_semantic_authority": false,
  "applicability_promoted": false,
  "claim_truth_promoted": false
}
```

The wrapper rejects missing source/revision pairs, digest drift, duplicate
receipts, promoted outputs, and SLR receipts with no corresponding Digital-ESD
request.

A process exit code of zero is **not** an evidence payment.


## Real ERIC corpus path

The 43,996-row fixture in the SLR repository is a **synthetic scale/regression
fixture**. It is not a parsed ERIC corpus and must not be cited as such.

The real Digital-ESD study path starts from the retained raw ERIC API exports
produced by `scripts/execute_digital_esd_eric.py`.

### 1. Parse the retained ERIC API pages

```bash
python3 interop_scripts/digital_esd_eric.py parse \
  --export-root artifacts/digital-esd/eric \
  --output artifacts/digital-esd/real-eric-studies.jsonl \
  --expect-occurrences 46597 \
  --expect-unique 43996
```

This verifies each retained raw page against its execution-summary SHA-256,
checks pagination/count completeness, and emits one row per stable ERIC
accession while preserving all Q1-Q7 memberships and raw-page provenance.

The parsed row contains real ERIC metadata such as:

```text
ERIC accession
title
abstract / description
authors
source
publication year
subjects
education levels
publication types
institution / publisher / sponsor
language
peer-reviewed metadata
URL / ERIC publication link
query membership
raw-page provenance
metadata revision SHA-256
```

Important:

```text
ERIC metadata parsed
!= screening decision

abstract parsed
!= paper/full-text parsed

ERIC full-text-available metadata
!= full text retrieved

cross-query overlap
!= duplicate empirical study
```

### 2. Materialise the authoritative unresolved screening ledger

The screening ledger compiler now accepts the parser's JSONL directly:

```bash
python3 scripts/prepare_digital_esd_screening_ledger.py \
  --input artifacts/digital-esd/real-eric-studies.jsonl \
  --out-dir artifacts/digital-esd/screening
```

Every real ERIC accession begins as `unresolved / awaitingScreeningReview`.

### 3. Build candidate-only assessments and study-family hypotheses

```bash
python3 scripts/assess_digital_esd_screening_candidates.py \
  --metadata artifacts/digital-esd/real-eric-studies.jsonl \
  --ledger artifacts/digital-esd/screening/screening-decisions.jsonl \
  --out-dir artifacts/digital-esd/screening/adaptive
```

These assessments may prioritise work but cannot write an include/exclude
decision.

### 4. Calibration + non-scalar Pareto work queue

```bash
python3 scripts/select_digital_esd_screening_pareto.py \
  --ledger artifacts/digital-esd/screening/screening-decisions.jsonl \
  --assessments artifacts/digital-esd/screening/adaptive/candidate-assessments.jsonl \
  --fibres artifacts/digital-esd/screening/adaptive/study-family-fibres.jsonl \
  --out-dir artifacts/digital-esd/screening/adaptive
```

### 5. Full text comes later

Only authoritative `include` / `probable` decisions enter:

`scripts/prepare_digital_esd_fulltext_handoff.py`

That is where actual PDFs/HTML/text are retrieved, hashed and lowered toward
the canonical SLR evidence substrate.

The existing `digital_esd_slr.py` wrapper begins **after** that point. It does
not parse ERIC metadata and it does not retrieve papers.


## Sparse full-text cache

The **43,996 ERIC records are metadata/screening records, not 43,996 local PDFs**.

Digital-ESD uses a sparse full-text working set:

```text
43,996 metadata rows
    ↓
title/abstract assessment + explicit screening
    ↓
include / probable only
    ↓
small bounded fetch batch
    ↓
local working cache
    ↓
parse / SLR interop
    ↓
optional GC of the working copy after downstream receipt
```

The cache controller is:

`interop_scripts/digital_esd_fulltext_cache.py`

It does not crawl the corpus or download documents itself.

### Plan a small batch

First generate the retained full-text worklist:

```bash
python3 scripts/prepare_digital_esd_fulltext_handoff.py \
  --ledger artifacts/digital-esd/screening/screening-decisions.jsonl \
  --out-dir artifacts/digital-esd/fulltext
```

Then select a bounded batch:

```bash
python3 interop_scripts/digital_esd_fulltext_cache.py plan \
  --worklist artifacts/digital-esd/fulltext/fulltext-worklist.jsonl \
  --priority-queue artifacts/digital-esd/screening/adaptive/screening-pareto-queue.jsonl \
  --cache-dir artifacts/digital-esd/fulltext/cache \
  --output artifacts/digital-esd/fulltext/fetch-batch.jsonl \
  --max-items 20 \
  --max-cache-gib 2 \
  --reserve-gib 5
```

The planner inspects actual filesystem free space and selects at most the
requested item count while respecting both the cache cap and the free-space
reserve. Unknown paper sizes use the explicit planning assumption
`--assumed-mib-per-item` (default 10 MiB); the hard byte cap is checked again
when retrieved files are registered.

### Register only what was actually retrieved

After an external/manual retrieval step emits a JSONL containing
`source_identity_reference`, `artifact_path`, `sha256`,
`retrieval_reference` and `retrieval_timestamp`:

```bash
python3 interop_scripts/digital_esd_fulltext_cache.py register \
  --plan artifacts/digital-esd/fulltext/fetch-batch.jsonl \
  --retrieved artifacts/digital-esd/fulltext/retrieved.jsonl \
  --output-ledger artifacts/digital-esd/fulltext/cache-ledger.jsonl \
  --max-cache-gib 2
```

Registration hashes the actual file and fails if it was not in the exact fetch
plan or would breach the hard cache cap.

### Eviction is receipt-gated

A working copy may be proposed for deletion only after a downstream parse/SLR
receipt exists and revision identity remains recorded:

```bash
python3 interop_scripts/digital_esd_fulltext_cache.py gc-plan \
  --cache-ledger artifacts/digital-esd/fulltext/cache-ledger.jsonl \
  --downstream-receipts artifacts/digital-esd/slr-interop/verified-receipts.jsonl \
  --output artifacts/digital-esd/fulltext/gc-plan.jsonl \
  --target-gib 1
```

`gc-plan` **does not delete files**. It emits an inspectable deletion plan.

Authority/storage boundaries:

```text
ERIC metadata says full text available != fetch obligation
43,996 metadata rows              != 43,996 papers on disk
include/probable                  != automatic download
downloaded                        != parsed
parsed                            != SourceAuditAdmission
cache eviction                    != loss of revision identity
```


## Actually parse retained studies

The sparse cache controller only plans and registers full-text artifacts.  A
registered artifact is **not** a parsed study.

Once include/probable papers have been retrieved and registered in:

```text
artifacts/digital-esd/fulltext/cache-ledger.jsonl
```

run the real scholarly parser through the thin Digital-ESD wrapper:

```bash
python3 interop_scripts/digital_esd_slr.py run-scholarly \
  --cache-ledger artifacts/digital-esd/fulltext/cache-ledger.jsonl \
  --slr-root ../slr \
  --slr-revision-reference "$(git -C ../slr rev-parse HEAD)" \
  --output-dir artifacts/digital-esd/slr-interop/scholarly
```

This performs:

```text
materialised cache artifact
    ↓ re-open + SHA-256 verification
same source/revision parser request
    ↓
SLR scholarly_parser_prototype.py
    ↓
anchored document nodes
candidate study facets
    ↓
same-object parse-bundle reconciliation
```

The resulting application-side parse receipts are:

```text
artifacts/digital-esd/slr-interop/scholarly/parse-receipts.jsonl
```

and may be supplied to the generic study-processing census as
`--slr-parse-receipts`.

Important authority boundaries:

```text
cache registration        != parsed study
parser success            != reviewed canonical evidence
candidate study facet     != study truth
parsed study bundle       != SourceAuditAdmission
```

The live SLR scholarly parser currently produces document-structure nodes and
candidate study facets such as Population, Sample, Intervention, Comparator,
Outcome, StudyDesign, Setting, Method, Limitation, Funding, Institution and
Measurement.

The parser remains a candidate extractor.  Review/payment and Digital-ESD
source-audit admission are later independent stages.
