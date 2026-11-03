# GenBank ingestion / avian magnetoreception change log

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
- DASHI/Codec/GenBankLocationFiniteCore.agda: Golden generic coordinate/start/strand proof terms.
- DASHI/Biology/GenBankInterpretationInteropExact.agda: existing DNA, protein, Wikidata/PNF and avian owner bridge.
- Imported both Agda modules into Codec/Biology/TOE roots; added synthetic regression tests and a source inventory.

### Verification ceiling
- Local synthetic parser prototype under Biopython 1.86: 7 tests passed.
- Local synthetic location roundtrip and Git-blob/feature parity positive and mutation checks passed.
- Original creator source was inspected via GitHub text, but exact original Biopython replay is not executed.
- Exact-head repository pytest, Agda kernel and Lean checks are outstanding.
- Not an in-vivo phenotype, successful gene edit or native ITIR/SLR repair authority.
