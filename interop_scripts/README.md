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
