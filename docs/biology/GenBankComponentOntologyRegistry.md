# Reusable GenBank genetic-component taxonomy and replicon provenance

Date: 2026-11-03. Owner: DASHI Codec/GenBank, source/evidence graph. Source parser:
`scripts/genbank_readonly_ingest.py`, built using Biopython (Cock et al.,
*Bioinformatics*, 2009, DOI 10.1093/bioinformatics/btp163).

**Goal:** Interpret any source-supplied GenBank feature annotation as a
source-bound candidate **without** treating a mobile element, gene, promoter,
plasmid, chromosome, or source label as a verified organism-level function.
This is a **read-only classification and evidence-reopening** capability.
It does not select genetic parts, design constructs, recommend insertion sites,
or provide DNA engineering protocols.

## Normative vocabulary and attribution

DDBJ/ENA/GenBank INSDC Feature Table Definition **v11.4, April 2026**:
https://www.insdc.org/submitting-standards/feature-table/

The original INSDC source feature *key* and qualifier spelling are retained.
The generic output adds only a projection class. No guessed external Sequence
Ontology/Wikidata identifier is equivalent to a source label.

- `gene` is a **gene annotation**; `CDS` a distinct **coding sequence
  annotation**, not a guarantee of an identified translated protein.
- `promoter`, `terminator`, `regulatory`, `polyA_signal` and related
  keys are **regulatory annotations**. A `regulatory` key needs its
  `/regulatory_class` to identify the subtype.
- `mobile_element` is the **only explicitly classed mobile element** in
  this bounded projection. Its `/mobile_element_type` (transposon,
  retrotransposon, insertion sequence, etc.) is recorded at source-annotation
  tier; no mobility assay is thereby established.
- `repeat_region` remains a **repeat annotation**. A label such as
  `transposon` on `misc_feature` or `repeat_region` does **not** promote
  it to the `mobile_element` feature class.
- `rep_origin` is a replication *feature*. It does not prove that the
  record is a plasmid or that any host-dependent replication occurred.
- `source` `/plasmid` and `/chromosome` are evidence for **record
  annotations**, not physical integration proof. A circular record with
  neither qualifier is **replicon-unresolved**. Contradictory claims remain
  a conflict, not a silent preferred value.
- Unknown/legacy keys and deficient required qualifiers produce **review
  holds**, not new ontology truth.

## Reused owners

- `DASHI.Codec.DNAFirstFormalism`, `DNACarrierFibre`: exact CAGT and
  quotient/complement geometry. **No second nucleotide representation.**
- `DASHI.Codec.GenBankLocationFiniteCore`: generic source start/width,
  strand and compound location owner.
- `scripts/genbank_readonly_ingest.py`: source parsed with full original
  locations and original qualifier arrays; no DNA bases emitted.
- `DASHI.Biology.Protein.TranslationContext`: selected-context translation,
  not inferred from a `CDS` label.
- `DASHI.Cognition.PNF.WikidataRepairProposal` and
  `DASHI.Ontology.WikidataRepairReopeningExact`: candidate-only no-promotion.
- ITIR-suite `itir-mcp/src/itir_mcp/wikidata_object_review.py`, and
  DASHI BH4 PR #1454's review worklist: **design pattern**, not a claim that
  this JSON is a conformant ITIR/SLR native API.
- Original records: Justin Atkin / The Thought Emporium retains design
  attribution. Nimpf/Wong and other paper authors retain their research
  attribution. The Thought Emporium's public repository states CC BY-SA 4.0.

## Executable contract

`scripts/genbank_component_registry.py` consumes the
`dashi.genbank.readonly.v1` report or parses the source via the existing
`parse_genbank_bytes` function. It emits:

- exact source key and ordered original location AST, one-based inclusive
  and zero-based half-open coordinates, qualifiers' **names**;
- a conservative `source_feature_class` and, only for `mobile_element`,
  optional source-typed subtype;
- separately recorded topology and replicon source-qualifier context;
- source identity, stable feature IDs and source-reopening refs;
- short, non-operational source label hints, suppressing edit/codon notes;
- explicit candidate-only review holds for uncertain/missing identities,
  invalid qualifiers or conflicting source labels;
- no DNA bases, redesigned sequences, biological function or public edits.

```sh
python3 -m scripts.genbank_component_registry \
  --genbank /path/to/source.gb \
  --creator "Original source creator" \
  --source-ref "https://original.example/source.gb" \
  --revision "source-revision-or-commit" \
  --output /tmp/feature-registry.json

python3 -m scripts.genbank_component_registry \
  --report /tmp/previous-genbank-report.json \
  --graph \
  --output /tmp/component-candidate-graph.json

python3 -m pytest -q tests/test_genbank_component_registry.py
agda -i . DASHI/Codec/GenBankComponentOntologyFiniteCore.agda
```

Executable reports are **source classification**, not observed wet-lab
outcomes, validated structural biology, external same-object protein matches
or physical arrangement. The original source blob SHA and document digest
remain distinct from semantic normalization.

## Current source examples (no design inference)

Source inspections through Justin Atkin's repository:

| Published file | Base count | Features | Mobile feature keys | Plasmid/chromosome source qualifier |
| --- | ---: | ---: | ---: | --- |
| `magnetoreception/paav syn with pigeonized human cacna1d.gb` | 11,214 | 22 | 0 | neither |
| `penicillin/penicillin_yeast_-_2020-04-17.gb` | 27,921 | 53 | 0 | neither |
| `p46815 empty yeast backbone.gb` | 6,981 | 20 | 0 | neither |

All three declare circular topology. **None may be automatically classified as
an evidenced physical plasmid from topology alone**; filenames and original
creator descriptions may be cited *as separate source assertions*.

The penicillin yeast file contains `CDS`, `promoter`, `terminator`,
`rep_origin`, `misc_feature`, `protein_bind` and `source` keys.
Several gene-like source labels appear on `misc_feature`, not `CDS`.
No DNA sequence or engineering assembly information is copied into this
classification document.

## Verification and remaining proof cut

- Local synthetic registry classifier and negative tests: **17 passed**.
- Original-file type/count/qualifier inspection: source read from original
  GitHub artifacts. These counts are **not** execution of the new registry
  against their byte-identical `.gb` files.
- Golden Agda taxonomy core will be **source-written**; exact-head kernel
  acceptance is open until an Agda referee actually executes.
- Native ITIR/SLR/PNF ingest requires a validated recipient adapter; the
  emitted candidate graph is intentionally not an API conformance claim.
- Full source-specific feature-to-protein identity, function and phenotype
  assertions require independent contextual evidence.

**Next exact max-cut:** run exact-head Python regression, run the classifier
on the original files with blob parity, check Golden Agda, and implement a
native read-only ITIR/SLR consumer handshake only after validating its contract.

The registry's `parser_location_rendering` is the **Biopython-parsed** view, not a claim of byte-for-byte source location syntax. The original GenBank source is reopened by its raw digest and original file reference; the normalized location AST retains exact coordinate, order and strand meanings.
