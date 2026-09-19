# Digital-ESD -> SensibLaw / SLR full-text review handoff

**Status:** Digital-ESD-side execution contract. This document does not modify
SensibLaw or SLR, does not admit studies, and does not promote extracted claims.

## Placement in the review pipeline

```text
database export
-> metadata deduplication
-> title/abstract screening
-> IncludedSourceLineage source
-> full-text retrieval + hash
-> SLR/SensibLaw review handoff
-> candidate source/span/PNF/review observations
-> explicit review acceptance
-> complete Digital-ESD SourceAuditAdmission
-> CorpusAuditedSource
```

SLR/SensibLaw is therefore a **second-stage consumer of screened full text**.
It is not the inclusion classifier and is not the source of review truth.

## Existing implementation donors checked

No SLR or SensibLaw implementation was modified.

### SLR runtime in this repository

`tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py`

The current implementation:

- accepts one source-unit row with `source_unit_ref`, `revision_ref`, language,
  source kind/role and either inline `text` or `text_path`;
- hashes the source text;
- requires a trained spaCy dependency parser;
- emits sentence-bounded PNF candidates with source spans;
- writes one record per source unit;
- keeps raw text out of the manifest;
- emits `candidate_only=true` and `semantic_promotion=false`;
- explicitly records that source role does not create claim truth and parser
  output does not create ontology truth.

`tools/slr-discourse-reconstruct/slr_wikipedia_article_pnf_world_producer.py`

The generic producer ABI used by the source-unit batch also retains:

- revision/snapshot identity;
- source-text SHA-256;
- source-span start/end coordinates;
- dependency-parser receipt;
- PNF candidate identity;
- candidate-only / non-promoting state.

Its QID-specific weld demonstrates a useful general rule: paying a surface
identity does not pay span/entity identity, property weld, semantic equivalence
or claim truth.

### Related Agda owners

- `DASHI/Interop/SLRWikipediaArticlePNFWorldProducerExact.agda`
- `DASHI/Interop/SLRNatClimateSourceUnitPNFBatchExact.agda`
- `DASHI/Wikimedia/SensibLawSourceUnitReviewHandoffExact.agda`

These already formalize the same candidate-only / no-promotion boundary.

### SensibLaw runtime

Reviewed SensibLaw revision:

`d25cddf73540bdbb313777bbf566280f4e34313b`

The public runtime/documentation describes SensibLaw as a deterministic
review/provenance layer. Its current compiler/review surfaces preserve
candidate identity, source-unit provenance, refined PNF, claim/target review
and promotion as separate states. Review-claim records carry review-only
evidence status and explicit provenance.

## Digital-ESD paper identity

Do **not** require a publication QID.

The existing concrete `SensibLawSourceUnit` Agda carrier has an `entityQid`
field because it was built for a Wikidata-oriented source-unit lane. Arbitrary
scholarly papers may legitimately have no publication QID.

The Digital-ESD bridge instead uses:

```text
AttributedSource source
ERIC ID? 
DOI?
PMID?
full-text artifact reference
full-text SHA-256
retrieval/snapshot reference
reviewed same-object identity reference
SLR source_unit_ref
```

where `?` means optional and independently verified.

```text
title equality != same-object publication identity
author QID != publication QID
missing publication QID != missing source identity
```

## Future JSONL handoff from screened full text

After screening/full-text retrieval, construct one JSON object per included
source for the existing SLR batch runner:

```json
{
  "source_unit_ref": "digital-esd:<stable-source-id>:<fulltext-sha256>",
  "source_kind": "scholarly-full-text",
  "source_role": "screened-digital-esd-study",
  "language": "en",
  "revision_ref": "fulltext-sha256:<sha256>",
  "text_path": "<retained full-text path>"
}
```

Optional metadata such as DOI/ERIC ID belongs in the Digital-ESD identity
sidecar; it must not be converted into a QID merely to satisfy another lane's
carrier.

Run the existing SLR batch without modifying it:

```bash
python3 tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py \
  --input-jsonl <digital-esd-fulltext-source-units.jsonl> \
  --output-dir <slr-record-dir> \
  --manifest <slr-manifest.jsonl> \
  --summary <slr-summary.json>
```

The resulting SLR record/manifest references can inhabit
`SLRSourceUnitAnalysisReceipt source` only after their source-unit identity is
same-object welded back to the corresponding `FullTextArtifactReceipt source`.

## Authority firewalls

```text
metadata candidate != SLR full-text input
screen inclusion != paper truth
full-text retrieval != SourceAuditAdmission
SLR source unit != publication identity
SLR PNF candidate != paper claim accepted as true
SLR residual != empirical fact
SLR review packet != raised claim ceiling
review acceptance != complete SourceAuditAdmission
SLR sidecar != corpus admission
```

The optional final product is:

```text
CorpusAuditedSource source
+
SLRSourceReviewPacket source
->
SLRAssistedCorpusAuditedSource source
```

The constructor requires the already-complete corpus-audited source. The SLR
sidecar therefore enriches a source without manufacturing its admission.

## When to execute this lane

Do not run deep SLR processing over the entire ERIC metadata corpus.

Use metadata/title/abstract screening first. Run SLR over the retained
full-text/probable-inclusion tranche, where source-span/claim/provenance
decomposition can materially reduce manual review work.

The Digital-ESD Pareto may use SLR residuals as **review priorities**, never as
source-quality or truth scores.
