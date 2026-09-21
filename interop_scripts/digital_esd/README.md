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


## Corpus-scale execution

The single-run controller above is useful for a smoke test. For the real retained
study corpus use the resumable sharded runner:

```bash
python3 interop_scripts/digital_esd/run_study_parse_corpus.py \
  --repo-root . \
  --fulltext-index artifacts/digital-esd/fulltext/verified-fulltext-index.jsonl \
  --out-dir artifacts/digital-esd/study-parse/retained-corpus-v1 \
  --purpose retained-study \
  --shard-size 128 \
  --jobs 1
```

Before launching the full corpus, run a bounded receipt-producing smoke test:

```bash
python3 interop_scripts/digital_esd/run_study_parse_corpus.py \
  --repo-root . \
  --fulltext-index artifacts/digital-esd/fulltext/verified-fulltext-index.jsonl \
  --out-dir artifacts/digital-esd/study-parse/smoke \
  --purpose retained-study \
  --shard-size 8 \
  --jobs 1 \
  --max-source-units 8
```

The corpus runner sorts source-unit identity deterministically, writes exact
shard JSONL inputs, executes the existing generic SLR parser independently per
shard, compiles candidate extraction packets, verifies parser-manifest and
packet counts, then aggregates the packets.

A shard is considered resumable only when its input hash and all recorded
output hashes still match its prior shard receipt. Changed or incomplete
outputs are recomputed.

The top-level receipt is:

`study-parse-corpus-manifest.json`

and records:

```text
verified full-text index hash
prepared source-unit hash
source-unit count
shard count
parsed source count
retained-study packet count
screening-resolution packet count
aggregate packet hashes
all_source_units_parsed_exactly_once
```

The formal receipt owners are:

```text
DASHI/Education/DigitalESDStudyParseExecutionExact.agda
DASHI/Education/DigitalESDStudyParseExecutionRegression.agda
```

A complete corpus parse is still **not** a reviewed or admitted corpus:

```text
parsed study
!= reviewed extraction
!= SourceAuditAdmission
!= CorpusAuditedSource
```


## First observed retained-study execution receipt

The first real retained study has now completed the concrete parse path:

```text
ERIC:EJ1083370
  -> PDF retrieval/cache
  -> source SHA-256
  -> pdftotext-layout materialisation
  -> derived-text SHA-256
  -> anchored document nodes
  -> candidate study facets
```

Observed receipt:

```text
source                    ERIC:EJ1083370
PDF bytes                 931903
source SHA-256            f48bad56d0874bb6ed2d109e10ebf495d30534e7e5ce74b8e5800541f6619b89
materialisation engine    pdftotext-layout
page count                30
derived characters        110188
derived-text SHA-256      cc248168e15089e8cb76a6ced160afc70e0ff64f74e01cd9140ae03d2eb679e0
anchored document nodes   1298
candidate facet families  13
```

The facet families are:

```text
Population
Sample
Intervention
Outcome
StudyDesign
Setting
TimePeriod
Method
Limitation
Funding
Institution
ParticipantGroup
Measurement
```

They remain locator candidates only. A matched Population/Outcome/etc span does
not establish the corresponding study fact and pays no extraction coordinate.

The formal observed receipt is:

`DASHI/Education/DigitalESDFirstRetainedStudyParseExact.agda`

with regression:

`DASHI/Education/DigitalESDFirstRetainedStudyParseRegression.agda`.

For a retained runtime artifact directory containing:

```text
requests.jsonl
verified.jsonl
parser-output.jsonl
```

verify the same-object execution receipt with:

```bash
python3 interop_scripts/digital_esd/verify_observed_study_parse_receipt.py \
  --receipt-dir artifacts/digital-esd/first-reviewed-study/study-facets-v0_2
```

The verifier checks source identity/revision/hash agreement, materialised-text
digest agreement, node/facet counts, the exact 13-role facet surface and every
candidate/non-promotion flag.

This execution receipt pays:

```text
real retained full text obtained
real PDF materialised
real anchored document nodes emitted
real candidate study-facet locations emitted
```

It still does not pay:

```text
reviewed Population/Sample/etc coordinate
study claim truth
nineteen-coordinate extraction completion
SourceAuditAdmission
CorpusAuditedSource
framework challenge conclusion
```
