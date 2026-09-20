# Digital-ESD study parse interop

This directory is a **thin application wrapper** around the existing generic SLR
source-unit PNF parser.

It exists to answer the concrete Digital-ESD question: once a study's full text
has been retrieved and same-object checked, how do we actually parse the study
and turn the parse into a reviewable extraction packet?

## Retained study lane

Input must already be an authoritative Digital-ESD full-text index row with an
explicit `include` or `probable` screening decision.

```text
verified full-text index
  -> prepare_slr_source_units.py
  -> tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py
  -> sentence-bounded dependency / PNF candidates
  -> compile_study_extraction_packets.py
  -> 19-coordinate candidate extraction packet
     + study-claim-ceiling coordinate
     + predicate-normal-form overlay
     + intersectional-absence overlay
     + material/environmental overlay
```

Run:

```bash
python3 interop_scripts/digital_esd/run_study_parse_pipeline.py \
  --repo-root . \
  --fulltext-index artifacts/digital-esd/fulltext/verified-fulltext-index.jsonl \
  --out-dir artifacts/digital-esd/study-parse/round-1 \
  --purpose retained-study
```

For a bounded smoke test add:

```text
--max-source-units 1
```

The underlying generic parser requires the configured local spaCy model (for
English, normally `en_core_web_sm`) with a dependency parser.

## Reviewed-unresolved screening-resolution lane

Full text fetched only because title/abstract review remained unresolved uses a
different purpose:

```bash
python3 interop_scripts/digital_esd/run_study_parse_pipeline.py \
  --repo-root . \
  --fulltext-index artifacts/digital-esd/screening-resolution/fulltext-index.jsonl \
  --out-dir artifacts/digital-esd/study-parse/resolution-round-1 \
  --purpose screening-resolution
```

Those records produce
`screening-resolution-parse-packets.jsonl`, **not** study-audit packets.

A later explicit `include` or `probable` decision is required before the same
source can enter the retained-study lane.

## What automatic parsing pays

It pays only structural parsing receipts:

- source-unit identity;
- full-text revision reference;
- source-text SHA-256;
- parser model/version;
- sentence count;
- candidate PNF observations;
- exact sentence character spans;
- sentence SHA-256;
- candidate lexical relevance to the existing 19 extraction coordinates.

It does **not** pay:

- any of the 19 extraction coordinates;
- the study claim ceiling;
- intersectional absence conclusions;
- deployment/material footprints;
- empirical claim truth;
- source quality;
- `SourceAuditAdmission`.

The extraction compiler therefore emits `coordinate_paid=false` and
`review_required=true` for every coordinate.

## Existing extraction target

The nineteen top-level coordinates remain owned by
`DigitalESDManuscriptMethodologyExact`:

1. source identity
2. source kind / evidence role
3. publication date
4. population / education level
5. jurisdiction / institutional context
6. digital technology / practice
7. pedagogy / curriculum / competence
8. sustainability dimension
9. study or review design
10. outcome or claim
11. time horizon
12. lifecycle boundary
13. circularity / repairability
14. participant agency / authority
15. interoperability / governance
16. externality incidence
17. same-object status
18. context transfer
19. uncertainty / limitation

`DigitalESDStudyClaimMethodBridgeExact` then retains the separate 20th
study-claim-ceiling coordinate and the PNF, intersectional-absence and
material/environmental overlays.

## Why this is not another parser architecture

The application wrapper calls:

`tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py`

unchanged. Digital-ESD contributes only source-unit preparation and a consumer
projection over the generic parser's candidate observations.

```text
new corpus != new parser
parser observation != reviewed extraction
reviewed extraction != SourceAuditAdmission
```
