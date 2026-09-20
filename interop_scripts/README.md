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
