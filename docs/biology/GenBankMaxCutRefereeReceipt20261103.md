# GenBank / DNA / ontology max-cut referee receipt — 2026-11-03

## Exact provenance and owners

- **Primary construct owner:** Justin Atkin / The Thought Emporium,
  `thethoughtemporium/Whose-gene-is-it-anyway`, original creator repository
  and README licensing (CC BY-SA 4.0).
- **Original file identities:** magnetoreception Git blob
  `0578ad167666789fbfd3faa849a455c25097b90c`;
  penicillin yeast `d350cf735f0a2061d0eb9ca006ed155c20f4034f`;
  yeast backbone `f0b0076aa86722004322f20185b9227459c8e90b`.
- **Existing mathematical owners:** `DNAFirstFormalism`,
  `DNACarrierFibre`, `DNAFourWayLiftOperators`,
  `GenBankLocationFiniteCore`, `ScientificMechanismEvidenceBidiExact`,
  `WikidataRepairProposal` and `WikidataRepairReopeningExact`.
  New finite source-coordinate proofs are DASHI-owned extensions, not
  original biological discoveries.
- **Parser:** Biopython 1.86; Cock et al., *Bioinformatics* (2009),
  DOI `10.1093/bioinformatics/btp163`.
- **ITIR native tool owner:** `itir-suite/itir-mcp/src/itir_mcp/domain_tools.py`,
  `wikidata_review_packet`, version
  `itir.wikidata.review_packet.v1`. Original ITIR contributors retain credit.
- **D-LSA empirical ownership:** Wong, Lim, Tan, Go, Bell, Freemont and Yew
  (2022), DOI `10.1038/s41467-022-28386-6`. The separate D-LSA PR #1459
  is not merged or imported as an unverified dependency.

## New max-cut deliveries on #1461

| Gate | Object | Acceptance recorded |
| --- | --- | --- |
| GB03-INVARIANT | `DASHI/Codec/GenBankFeatureGeometrySymmetryExact.agda` | Source-written **Golden** bounded interval/strand order source geometry; proof terms for coordinate normalization commuting square, mirror geometry involution and ordered compound feature observation |
| GB03-INDEX | `DASHI/Biology/GenBankCanonicalDNAFibreIndexExact.agda` | Source-written non-Golden vector-length indexed transport, all finite index lookup/encode laws and fibre reconstruction using existing DNA base carrier |
| GB04-REFERENCE | `scripts/check_genbank_feature_geometry_square.py` and regression tests | Python checker source-written; local independently constructed 2,000 synthetic Biopython 1.86 geometry cases passed, **0 mismatches**; 1,471 mixed child strand cases |
| GB04-SOURCE | `data/ThoughtEmporiumThreeSourceGeometryIndependentAudit.json` | Independent original creator **95** feature-location strings inspected; 22/53/20 features, 1 compound feature, 25 complemented span annotations; exact span bounds and double mirror passed |
| GB07-ITIR-INPUT | `scripts/genbank_itir_native_review_adapter.py` and tests | Source-written input matching actual reviewed `itir_mcp.domain_tools.wikidata_review_packet` call shape. Optional real imported native execution refuses to issue a receipt if package unavailable. All GenBank features remain source-annotation candidates |
| P0-DOC | `docs/biology/GenBankInteropTODO.md` | Reconciled original-file parsing/semantic roundtrip completed locally vs exact-head/python and Agda kernel gates OPEN. Python package invocations corrected to `python3 -m scripts.X` |

### Important bug corrected during referee

A naive source geometry mirror reversed the order of every compound feature.
This **does not agree with Biopython**. Biopython 1.86's
`CompoundLocation._flip` reverses part order **only if all direct child
part strands are None**. If any child has a defined strand, part order is
preserved, even if the aggregate compound `strand` is itself None due
to mixed parts. The Golden theorem now represents this as distinct
`allPartsWithoutStrand` versus `atLeastOneStrandedPart` constructors.
The Python checker now matches the real library's policy.

Separate local randomized independent harness: **2,000 cases, zero errors**,
with five source lengths (8,17,64,127,256), randomized exact spans and
2–5 part joins/order. Of these, 1,471 had mixed child strand assignments,
529 were homogeneous/single. Source-level audit of original 95 feature
coordinate strings also passed, but is **not** the exact committed Python
checker run against all original bytes.

### Verification categories — do not conflate

- **Executed locally:** 2,000 independent toy Biopython reference
  geometry tests; source coordinate inspection of 95 original annotations;
  earlier 17 local synthetic component registry tests; previous original
  magnetoreception local prototype source parse/22 feature and semantic
  roundtrip receipts.
- **GitHub source-written/readback:** Golden geometry and non-Golden vector
  proof definitions, Python geometry/source and native ITIR adapters/tests,
  canonical `DASHI/Everything`, `Codec/Everything`,
  `Biology/Everything` imports. No visible `postulate`, Agda holes or
  TERMINATING escapes in newly authored Golden source.
- **NOT executed:** exact-head GitHub branch pytest, Golden Agda kernel,
  non-Golden indexed proof checker, native installed ITIR library call on
  these source feature candidates, or SLR/ITIR persistence consumer.
  The available local environment had Biopython 1.86 and pytest 9.0.2,
  but no Agda executable and no DNS access for GitHub clone. GitHub
  combined status/workflow lookup for the pre-work #1461 head returned none.
- **NOT mathematically proved:** universal correctness of Biopython
  raw GenBank parsing; refinement to the Golden n-ary source AST with
  missing/mixed feature strand proofs; all circular rotation properties;
  semantic biological gene/protein same-object or phenotypic conclusions.

## Exact remaining obligations after these commits

1. **Kernel receipt:** checker version, exact tree SHA and Agda --safe
   acceptance of `GenBankFeatureGeometrySymmetryExact`, and ordinary
   Agda acceptance of `GenBankCanonicalDNAFibreIndexExact` and
   biology/Codec/root import graph.
2. **Actual checker against all three original sources:** obtain exact
   blob-pinned local files, run committed Python source geometry checker,
   full GenBank roundtrip and component classifier on the same blobs.
3. **Parser refinement:** relate the actual Biopython n-ary
   `CompoundLocation` (all child strand predicates) to the binary
   Golden feature geometry and preserve original order, coordinates,
   feature identity and raw/semantic SHA distinction.
4. **Native interface execution:** install or point to exact-version
   `itir_mcp`, run input adapter native call, verify output
   `itir.wikidata.review_packet.v1` and source reopening, then test
   native PNF/SLR read-only consumer if a compatible API exists.
5. **Biology claims:** source-pay external accession/isoform, translation,
   transcript and organism context; separately W22-01..05 for the
   publisher's original D-LSA assays, analytics and metabolism.

## Commands (run from DASHI repository root)

```sh
python3 -m pip install -r requirements-genbank.txt
python3 -m pytest -q tests/test_genbank_*.py
python3 -m scripts.check_genbank_feature_geometry_square /path/to/original.gb
python3 -m scripts.genbank_component_registry --genbank /path/to/original.gb --output /tmp/genbank-components.json
python3 -m scripts.genbank_itir_native_review_adapter /tmp/genbank-components.json --output /tmp/itir-input.json
python3 -m scripts.genbank_itir_native_review_adapter /tmp/genbank-components.json --itir-src /path/to/ITIR-suite/itir-mcp/src --execute-native --output /tmp/itir-native-receipt.json
agda -i . DASHI/Codec/GenBankFeatureGeometrySymmetryExact.agda
agda -i . DASHI/Biology/GenBankCanonicalDNAFibreIndexExact.agda
agda -i . DASHI/Everything.agda
```

**Scientific/ontology firewall:** genetic element labels and mathematical
sequence symmetries do not establish experimental expression, actual
transposition, organism-level perception, biosynthetic performance,
human effects or permission to alter public ontologies. No original DNA
bases, genetic engineering protocols or D-LSA production recommendations
are emitted in this tranche.
