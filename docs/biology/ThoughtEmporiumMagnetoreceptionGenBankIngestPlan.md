# The Thought Emporium magnetoreception GenBank interpretation → DASHI integration

**Status (3 November 2026, implementation tranche):** Source inspection and feature inventory are committed, as are a **reusable read-only Biopython-based GenBank parser**, a separate original Git-blob/feature-location parity verifier, a **Golden** source-written Agda location core, a non-Golden adapter that reuses the existing DNA/protein/repair owners, and candidate-only graph/worklist emitters. A local prototype of the reusable parser passed **7 synthetic tests** and source-parity mutation exercises. **The published original GenBank has not been run through the Python importer on an exact GitHub checkout; Agda/Lean kernel acceptance, exact-head pytest and native ITIR/SLR API compliance remain unverified.** No sequence-to-function or human phenotype claim is established.

**Primary interpretation finding:** the creator's source label \`"cacna1d human plus pigeon"\` is attached to **feature index 8, \`misc_feature\`**, not a \`CDS\`. The only two \`CDS\` feature labels are \`"Factor Xa site"\` and \`"AmpR"\`. This does not disprove the suggested coding function, but it means the file's own feature table does **not** carry an explicit gene/CDS/translation witness for the presumed target. Preserve this as a review hold, not a fabricated translation.

## Actual-original-byte local verification receipt — 3 Nov 2026

**GB02-REAL (local prototype) is paid.** Exact original creator file bytes were reconstructed locally from the original GitHub source, then independently checked against the original Git blob SHA `0578ad167666789fbfd3faa849a455c25097b90c`. The resulting 18,278-byte file was parsed with Biopython 1.86; it gave **11,214 concrete DNA bases**, **circular ds-DNA**, **22/22 source features in original order**, and **0 feature-geometry/strand/compound/qualifier discrepancies** under the source parity checker. Raw SHA-256: `43e7f588788e36c7a3b7d4e794dde21311781a9eae9fd857fe5cac79b46f03d1`. Normalized sequence SHA-256: `7e1449a229c1182bc787bf861a906b42313e5e0d6676770a9d8bfa0a7bbd71db`.

The source-derived candidate-only projection produced **22 feature statements and 30 reopening/identity review holds** (22 source-label-to-external-identity; eight missing CDS gene/product/translation/codon_start fields). The local synthetic parser test suite yielded **7 passed / 0 failed**. See `docs/biology/data/ThoughtEmporiumMagnetoreceptionLocalExecutionReceipt.json` for the bounded machine-readable receipt; no original bases are distributed.

**Do not overpromote:** these commands used a locally executed prototype corresponding to the PR scripts, **not the exact PR checkout**. The full exact-head pytest acceptance, Agda kernel, full-record parser/serializer roundtrip and native ITIR/SLR ABI are still OPEN. Neither source structure nor candidate ontology graph validates a realised protein or magnetic sense.

## Primary object and original ownership

The original design belongs to **Justin Atkin / The Thought Emporium** and is available at:
- Repository: https://github.com/thethoughtemporium/Whose-gene-is-it-anyway
- Source file: `magnetoreception/paav syn with pigeonized human cacna1d.gb`
- Original Git blob SHA: `0578ad167666789fbfd3faa849a455c25097b90c`
- Upload commit: `f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d` (2020-07-04T03:23:52Z).
- License statement: repository README, Creative Commons Attribution-ShareAlike 4.0; credit the original creator, and preserve derivative licensing where applicable.
- The June 17 2020 stream transcript is a **different source**. It describes the reasoning and the unfinished work at that time. The `.gb` is a later uploaded digital artifact.

Metadata-only inspection of the actual file through the connected GitHub source:
- `LOCUS`: **11,214 bp, ds-DNA, circular**, **16-JUN-2020** internal header date.
- `ORIGIN`: 11,214 A/C/G/T characters; end marker `//` present.
- `FEATURES`: **22 annotations**: 9 `primer_bind`, 2 `promoter`, 2 `rep_origin`, 1 `polyA_signal`, 3 `repeat_region`, 2 `misc_feature`, 2 `CDS`, 1 `source`.
- One `join(...)` compound location, seven `complement(...)` feature locations.
- Annotation qualifier names observed: `/label`, `/ApEinfo_revcolor`, `/ApEinfo_fwdcolor`. Neither CDS declares `/gene`, `/product`, `/translation`, or `/codon_start`.
- `DEFINITION` contains a dot; an `ACCESSION` or `VERSION` line was not observed. This is a user-designed GenBank-format artifact, not necessarily an accessioned GenBank database entry.
- Both the GenBank internal header date and GitHub upload timestamp are retained with different provenance roles. Neither alone proves digital completion on that specific date.

These are **inspected file-structure claims**, not a claim of biological correctness. The sample's original raw sequence is not redistributed by this roadmap.

## Already in repository: reuse order

1. **Core DNA carrier**: `DASHI.Codec.DNAFirstFormalism.Base`, `List Base`, `complement`, `reverseComplement`. `DASHI.Codec.DNACarrierFibre` already contains encoding/decoding and complement-equivariant lemmas. Reuse, do not redefine an incompatible base alphabet.
2. **GenBank topology and features**: no exact `GenBank` parser/AST owner was found by default-branch GitHub code search. Introduce one small, **canonical** GenBank syntax owner for parseable metadata, circular/linear molecule, interval/location expressions, strand and qualifiers. A feature must retain its *source text* and a normalized view. A location AST must represent spans, `join`, `complement`, potential fuzzy bounds and circular origins, not collapse every location into one forward interval.
3. **Contextual transcript/protein interpretation**: `DASHI.Biology.Protein.TranslationContext`, `DASHI.Promotion.ProteinEncoding`, `DASHI.Promotion.TranslationContextEncoding`. A `CDS` label is NOT automatically a selected transcript/translation witness. The file lacks explicit translation and reading-frame qualifiers; those are source-bound obligations, not defaults silently promoted to empirical facts.
4. **Biological cross-scale**: `DASHI.Biology.NeurochemicalGenomicExpressionBridge`, `GenomeSensorimotorConnectomeBridge`, `MagnetoreceptionSurface`, and `AvianMagnetoreceptionThoughtEmporiumEvidenceExact`. Connect the source object to the *vestibular candidate* and other existing mechanism owners through claims and context, not sequence -> sense as a total function.
5. **Source/PNF and governance**: `DASHI.Core.AttributedSourceCore`, `DASHI.Interop.AvianCompassPNFSemanticBridge`, and `DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact`. Distinguish `publishedDigitalArtifact`, `parsedSequence`, `sourceAnnotation`, `sequenceIdentityVerified`, `proteinInterpretation`, `reportedExperiment`, `validatedPhenotype` as *independent receipts*. The text PNF graph is an indexed evidential view, not a science theorem.

**Not a GenBank importer:** `DASHI.Codec.DNAProductionConstraints` and `DNAProductionNormalization` describe a *generative* constrained DNA code / normalization machine, not a biological guarantee or blanket compliance test for externally authored sequences. Reuse only for structurally appropriate optional analysis; do not make them ingest-gating requirements.

## Concrete source-written implementation (this PR)

| Source | Purpose | Acceptance level |
|---|---|---|
| \`scripts/genbank_readonly_ingest.py\` | Reusable strict Biopython \`SeqIO\` parser; normalized 0-based half-open spans, source 1-based inclusive labels, \`join/order\` locations, complements, circular/linear topology, source and semantic hashes, qualifier order, no emitted DNA sequence | Local synthetic parser tests executed, original same-object full-byte run open |
| \`scripts/check_genbank_source_inventory.py\` | Independent source Git-blob SHA-1, 22-entry feature inventory and source-location spelling parity; reject feature-order/strand/coordinate/qualifier drift | Local synthetic parity and mutation check executed; original file run open |
| \`scripts/genbank_ontology_review.py\` | Candidate-only, source-reopenable ontology review holds modelled on BH4 and ITIR user stories; no live Wikidata edits | Local synthetic worklist check executed; native ITIR/SLR interface open |
| \`DASHI/Codec/GenBankLocationFiniteCore.agda\` | Golden \`--safe\` generic location type, positive source-start encoding, 0/1 coordinate and strand-involution lemmas | Source written; Agda kernel pending |
| \`DASHI/Biology/GenBankInterpretationInteropExact.agda\` | Existing \`DNAFirstFormalism\`/\`DNACarrierFibre\`, \`Protein.TranslationContext\`, situated protein, creator attribution, Wikidata repair/reopening and avian PNF proof-owner reuse | Source written; exact-head kernel pending |
| \`docs/biology/data/ThoughtEmporiumMagnetoreceptionGenBankSourceInventory.json\` | Independent source-text inspection: immutable creator Git blob, 11,214 base count, all 22 original feature types, source labels, location text, qualifier names, and non-authority flags; does not redistribute bases | GitHub readback and deterministic source inspection completed |
| \`tests/test_genbank_*.py\` | Synthetic parser/roundtrip, source fixture, original metadata, ontology nonpromotion and mutation checks | Author-written on branch; exact-head pytest pending |

The source-inventory feature table is **not an automatically generated assertion of correct translation**. It is a bounded source-text transcription. Independently replaying the Python importer against the exact original bytes is the next required step. \`DNAProductionConstraints\` remains an unrelated generative codec policy and never screens or modifies this imported source.

### Reproduce on a checkout with the original author file available

Use the original creator's publicly attributed GenBank file. Do not modify it. The following commands **read and summarize it without emitting sequence bases**:

\`\`\`sh
python3 scripts/genbank_readonly_ingest.py /path/to/original.gb \
  --creator "The Thought Emporium / Justin Atkin" \
  --source-ref "https://github.com/thethoughtemporium/Whose-gene-is-it-anyway/tree/master/magnetoreception" \
  --revision "f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d" \
  --output /tmp/magnetoreception-source-report.json

python3 scripts/check_genbank_source_inventory.py /path/to/original.gb

python3 scripts/genbank_ontology_review.py \
  /tmp/magnetoreception-source-report.json \
  --output /tmp/magnetoreception-review-holds.json

python3 -m pytest -q \
  tests/test_genbank_readonly_ingest.py \
  tests/test_genbank_source_inventory.py \
  tests/test_genbank_ontology_review.py \
  tests/test_genbank_creator_source_inventory.py

agda -i . DASHI/Codec/GenBankLocationFiniteCore.agda
agda -i . DASHI/Biology/GenBankInterpretationInteropExact.agda
\`\`\`

The Agda commands may require the repository's existing standard-library include configuration and compatible toolchain. An Agda source file and a static byte inventory do not substitute for an actual accepted kernel check.

### Source-specific same-file crosswalk

The reusable parser is kept generic. The separate `scripts/genbank_magnetoreception_crosswalk.py` invokes it and **requires successful original Git-blob parity in the same process** before linking the exact source feature labelled `cacna1d human plus pigeon` (index 8, `misc_feature`) to the Nimpf 2019 vestibular hypothesis and Justin Atkin's June 2020 discussion. It retains the original creator/paper-author distinction and marks both CRY4 and hepatic-macrophage research as **later contextual comparisons**, not parts identified in the 2020 GenBank file. The output's same-object protein, phenotype, public ontology edit, and native ITIR/SLR acceptance flags are all false.

To reproduce after obtaining original bytes, also run:

```sh
python3 scripts/genbank_magnetoreception_crosswalk.py /path/to/original.gb \
  --output /tmp/magnetoreception-source-crosswalk.json
```

Its source-written implementation and synthetic contract tests do **not** mean the exact creator-byte parity has been executed on this branch.

## Exact implementation cut

| Gate | Deliverable / owner | Acceptance |
|---|---|---|
| GB01 — immutable source | `scripts/extract_magnetoreception_gb.py` metadata-only sidecar and original-source ref | Ref pins exact blob SHA, size, ownership, license, internal header date and external commit timestamp; does not copy proprietary external sequences by default |
| GB02 — independent executable ingest | Strict parser (e.g. Biopython `SeqIO` plus explicit input validation) and `tests/test_magnetoreception_genbank_ingest.py` | 11,214 bases, DNA alphabet, circular declaration, 22 source annotations, all feature coordinates within source, annotation counts, orientation and `join/complement` handling verified. Invalid/fuzzy/unsupported locations fail visibly, rather than truncate silently |
| GB03 — exact typed object | `DASHI.Codec.GenBankDocumentExact` and non-operational Python-to-Agda witness generator | `GenBankRecord` includes sequence length/topology, base carrier, `LocationAST` (interval, join, complement), original qualifier map, source hashes. Typed invariants distinguish 1-based inclusive source coordinates from internal 0-based half-open coordinates. Real witness should be checked from actual parsed data, not manually selected constants |
| GB04 — lossless/semantic round-trip | `GenBankRoundTrip` receipt and executable fixture/negative regression | `parse(serialize(normalize(parse(source))))` preserves semantic AST; raw bytes are retained separately so reformatting is not falsely called byte-identical. Prove coordinate and orientation reconstruction; reject a one-base off-by-one and a swapped complement |
| GB05 — crosswalk to study and transcript | `DASHI.Biology.MagnetoreceptionGenBankSourceBridgeExact` | Link 2020 stream timestamped claims, 2019 Nimpf hypothesis, record feature **labels** and later paper evidence as distinct source assertions; `pigeonized human cacna1d` is an attributed design label, not independently proven human-pigeon orthology or function |
| GB06 — contextual translation | Existing `Protein.TranslationContext` / `Promotion.ProteinEncoding` adapters | No reading frame/translation inferred without explicit selected context. Evidence must identify coding strand, frame, selected transcript/isoform and authoritative source before a same-object protein annotation is claimed; encode unresolved as a residual |
| GB07 — PNF/ontology graph | Extend existing `AvianCompassPNFSemanticBridge` with explicit evidence nodes/edges | Typed edges `artifactHasFeature`, `featureLabelClaimsIdentity`, `transcriptMentionsStudy`, `studySupportsHypothesis`, `measuredSensoryEffect`; every edge carries creator/source/version and confidence tier. No text claim promoted to validated physical ability |
| GB08 — Golden acceptance and docs | `DASHI/Codec/Everything.agda`, `DASHI/Biology/Everything.agda`, `DASHI/Everything.agda`; roadmap/tests/changelog | Agda Golden `{-# OPTIONS --safe #-}` (0 postulates, 0 metas, 0 terminating escapes), exact-head compiled roots, actual parser tests, negative tests, source SHA/commit receipts and updated docs in-step |

## Expected outputs to a downstream consumer

A deterministic, provenance-rich **interpretation report** with:
- explicit source/creator attribution and a file-identity receipt;
- structured feature inventory, circular topology and normalized location AST;
- selected feature-to-source-claim matches and unresolved annotation identities;
- biology/cellular/sensory concept links to existing DASHI owners and external ontology IDs where source-backed;
- no validated phenotype claim unless independently justified;
- machine-readable JSON for inspection plus **kernel-checked Agda certificates** when checker is available.

The original source GenBank content may remain in an immutable external source location with exact SHA and terms; DASHI initially consumes metadata and generated typed summaries. If redistribution of the original sequence is desired later, review attribution/share-alike terms and preserve it as **read-only original**, never silently rewrite original authorship.

## Scientific and security boundary

This work is for **interpretation and source validation**, not design of human interventions. No guides, sequence edits, target optimization, delivery routes, experimental protocols or executable plasmid construction plans belong in this integration. Computational validity of a GenBank file does not establish expression, tissue targeting, neural coupling, magnetic perception, safety or any same-species cross-context transfer.

**First highest-value implementation:** GB02/GB03 source-first parse and formal witness, then GB04 semantic round-trip, then GB05/GB07 biology and PNF joins. The 2020 stream supplies motivation and evidence about design decisions; the GenBank artifact is the authoritative object for a claim about what its actual annotations contain.
