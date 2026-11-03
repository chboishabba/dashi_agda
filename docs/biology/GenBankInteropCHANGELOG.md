# GenBank ingestion / avian magnetoreception change log

### Original source bytes exercised after source-writing
- The exact original GitHub creator source was reconstructed locally, independently confirmed against Git blob SHA `0578ad167666789fbfd3faa849a455c25097b90c`, then parsed with local Biopython 1.86 prototype.
- Local original run: 18,278 bytes; 11,214 DNA bases; circular ds-DNA; all 22 source annotations in original order; source geometry/qualifier parity **PASS, zero discrepancies**.
- Local candidate-only ontology projection: 22 source-annotation statements and 30 reversible lookup/annotation worklist holds.
- Local synthetic parser tests: 7 passed, 0 failed. Bounded receipt: `docs/biology/data/ThoughtEmporiumMagnetoreceptionLocalExecutionReceipt.json`.
- Exact-head pytest/Agda/Lean, native ITIR/SLR ABI and independently tested biology are not included in these claims.

## 2026-11-03 — Source → reusable parsing and candidate review

### Attribution and documentation
- Original digital construct attributed to Justin Atkin / The Thought Emporium; creator's GitHub repository states CC BY-SA 4.0.
- Biopython original authors credited for GenBank parsing; existing BH4/Kitzerow, DNA codec and ITIR/SensibLaw theorem owners are reused.
- Pinned non-sequence original inventory: 11,214 bases, 22 features, circular DNA, one joined and seven complemented locations.
- Flagged that the original source label containing cacna1d is a misc_feature, not a CDS annotation.

### Code
- scripts/genbank_readonly_ingest.py: reusable read-only sequence-free GenBank AST report and candidate graph.
- scripts/check_genbank_source_inventory.py: independent original Git-blob, coordinate/strand, feature and qualifier parity checks.
- scripts/genbank_ontology_review.py: candidate-only source reopening and unresolved external protein/ontology identity worklist.
- scripts/genbank_magnetoreception_crosswalk.py: strict original-source-parity-gated candidate feature-to-2019 vestibular hypothesis link; CRY4/hepatic only contextual.
- DASHI/Codec/GenBankLocationFiniteCore.agda: Golden generic coordinate/start/strand proof terms.
- DASHI/Biology/GenBankInterpretationInteropExact.agda: existing DNA, protein, Wikidata/PNF and avian owner bridge.
- Imported both Agda modules into Codec/Biology/TOE roots; added synthetic regression tests and a source inventory.

### Verification ceiling
- Local synthetic parser prototype under Biopython 1.86: 7 tests passed.
- Local synthetic location roundtrip and Git-blob/feature parity positive and mutation checks passed.
- Superseded by the subsequent executed local replay below: the exact original source's raw Git blob was verified and Biopython parsed all features with zero parity mismatches. The GitHub branch's own exact-head test execution remains outstanding.
- Exact-head repository pytest, Agda kernel and Lean checks are outstanding.
- Not an in-vivo phenotype, successful gene edit or native ITIR/SLR repair authority.


### Executed original full-record semantic roundtrip
- The exact original creator file passed Biopython parse/serialize/parse locally: sequence hash and length, molecule type/topology, annotated feature types, every original feature location and qualifier array, and record ID all preserved.
- Serializer rewrote formatting (18,278 original bytes → 18,377 normalized bytes). This demonstrates **semantic**, not byte-exact, roundtrip. The creator's original raw file SHA remains separate.
- Added `scripts/check_genbank_semantic_roundtrip.py` and a generic synthetic parser roundtrip test. Formal all-input correctness and exact-head kernel acceptance remain open.
