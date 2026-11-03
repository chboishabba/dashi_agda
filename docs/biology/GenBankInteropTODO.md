# Canonical GenBank → Golden DNA codec → read-only ontology max-cut

Updated 2026-11-03. Source owner: Justin Atkin / The Thought Emporium
for the original three published GenBank files; Biopython authors own the
GenBank parser. DASHI existing DNA/Protein/Wikidata theorem owners remain
canonical. No ESD edits, external ontology edits or operational DNA designs.

## A. Source-verified and implementation-complete steps

- [x] GB01: pinned original magnetoreception creator Git blob SHA, upload
  commit, CC BY-SA repository notice; raw-versus-normalized identities distinct.
- [x] GB02-LOCAL: local Biopython 1.86 original magnetoreception byte
  reconstruction/parse, 11,214 bases, 22/22 feature parity, zero reported
  source geometry/qualifier mismatches. Local prototype, not exact repo head.
- [x] GB02-GENERIC: read-only strict GenBank parser, nested exact spans,
  origin-wrapping compound parts, strand and original ordered qualifiers.
- [x] GB03-SOURCE: source-written Golden location and component taxonomy
  owners. No postulates, unsolved metas or TERMINATING pragmas visible in
  these authored source files; **Agda kernel has not run**.
- [x] GB03-INDEX: source-written non-Golden all-length canonical DASHI Base
  vector → existing ChemicalPair/ComplementPhase fibre → Base reconstruction
  with finite lookup/encoding commutation lemmas.
- [x] GB04-LOCAL: original magnetoreception Biopython parse→write→parse
  preserved seven semantic checks. Original 18,278 bytes and normalized
  serialization 18,377 bytes are intentionally NOT called byte-identical.
- [x] GB04-MODEL: new Golden finite source-length bounded span,
  source/in-memory coordinate normalization square, strand involution,
  and ordered compound-location semantic double-reversal lemmas.
- [x] GB04-REFERENCE: source-written Python mirror comparison against
  Biopython 1.86; independent local test matched 2,000 toy feature cases,
  including 1,471 mixed-strand cases, with zero mismatches. The correct
  Biopython rule reverses compound parts only if **all** child strands
  are unspecified; otherwise part order is retained.
- [x] GB04-ORIGINAL-METADATA: independent source-text coordinate and
  double-reversal audit of all 95 features across the three original
  creator files; original Git blob identities and receipt committed.
  This does not execute the new Python geometry checker on source bytes.
- [x] GB05-LEDGER: source feature index 8 labeled cacna1d is a
  misc_feature, NOT one of the two annotated CDS; Nimpf relation is a
  candidate creator-context link, not empirical protein evidence.
- [x] GB07-CLASS: generic INSDC key classifier, separate mobile/repeat
  gene/CDS/regulatory types and topology/replicon source claims; original
  three-file source inspection reports 22, 53 and 20 feature annotations.
- [x] GB07-SYNTHETIC: 17 locally passing component taxonomy tests, with
  negative cases; source-equivalent GitHub readback checked.
- [x] GB07-ITIR-INPUT: actual ITIR-suite domain_tools.wikidata_review_packet
  **input contract** adapter source-written, with a call to native function
  conditional on real ITIR package availability. This is not an executed
  native acceptance receipt.

## B. Exact remaining acceptance/payment obligations

- [ ] GB08-PYTEST: run the PR's **exact current head**, all focused
  read-only parser, feature geometry, component, source fixture,
  ontology and native-adapter tests in a real repo checkout. Local
  synthetic/prototype execution is not a substitute.
- [ ] GB03-KERNEL: run agda --safe on Golden location, component and
  feature geometry modules, and check non-Golden DNA-index/biology adapters
  and canonical roots with the repository's actual stdlib/toolchain.
  Preserve 0 postulates, 0 unsolved metas, 0 TERMINATING pragmas.
- [ ] GB04-REFINEMENT: formally connect actual serialized GenBank parser
  text and arbitrary-length n-ary Biopython compound location ASTs to
  Golden binary semantic model (including exact child strand/order policy).
  The present Golden theorem proves the model, not universal parser code.
- [ ] GB04-REAL-RC: run committed `check_genbank_feature_geometry_square.py`
  on exact original creator bytes for all three records. Independent
  original source-string audit is not that same-object execution.
- [ ] GB05-TRANSCRIPT: align each relevant original video timestamp
  with the later source artifact's feature labels; locate changes and
  divergences without manufacturing biological/protein equivalence.
- [ ] GB06-PROTEIN: independently source-match gene/product annotations to
  accession, revision, organism, isoform, reading frame, transcript and
  genetic code before same-object protein classification.
- [ ] GB07-ITIR-NATIVE: execute the native ITIR-suite
  itir_mcp.domain_tools.wikidata_review_packet against the exact
  generated candidate input, verify version, source reopening and
  non-promotion, and test any additional native SLR/PNF persistence
  handshake in a read-only fixture. No public Wikidata edits.
- [ ] GB07-BH4: reconcile external-source identity and review worklist
  interfaces with unmerged BH4 PR #1454, without replacing that owner.
- [ ] GB08-REFEREE: attach exact source commit/tree SHA, tool versions,
  tests, kernel output and explicit remaining empirical assumptions.
- [ ] GB08-LEAN: optional Lean mirror only after Golden owner has actual
  kernel acceptance; avoid another parallel DNA base carrier.
- [ ] W22-01..05: publisher source-data authenticity, stereochemistry,
  replicate/assay evidence and real metabolic state/kinetic/transport
  witnesses in separate D-LSA PR #1459. This cannot be paid by reading
  a GenBank file or by a formal sequence symmetry identity.

## Reproduction entrypoints (non-operational/source-read-only)

```sh
python3 -m pip install -r requirements-genbank.txt
python3 -m pytest -q tests/test_genbank_*.py
python3 scripts/check_genbank_source_inventory.py /path/to/original.gb
python3 scripts/check_genbank_semantic_roundtrip.py /path/to/original.gb
python3 scripts/check_genbank_feature_geometry_square.py /path/to/original.gb
python3 -m scripts.genbank_component_registry --genbank /path/to/original.gb --output /tmp/components.json
python3 scripts/genbank_itir_native_review_adapter.py /tmp/components.json --output /tmp/itir-input.json
python3 scripts/genbank_itir_native_review_adapter.py /tmp/components.json --itir-src /path/to/ITIR-suite/itir-mcp/src --execute-native --output /tmp/itir-native-receipt.json
agda -i . DASHI/Codec/GenBankFeatureGeometrySymmetryExact.agda
agda -i . DASHI/Codec/GenBankComponentOntologyFiniteCore.agda
agda -i . DASHI/Biology/GenBankCanonicalDNAFibreIndexExact.agda
agda -i . DASHI/Biology/GenBankInterpretationInteropExact.agda
```

**Provenance firewall:** computational source-annotation consistency is NOT
proof of gene/protein same-object identity, actual mobile-element mobility,
plasmid replication, construct expression or organism-level phenotype.
