# GenBank read-only source integration TODO — 2026-11-03

Owner: DASHI DNA codec × attributed biology × ITIR/SensibLaw candidate repair interop.
Original source: Justin Atkin / The Thought Emporium. Parser: Biopython.

## Source-written completion

- [x] Original GitHub GenBank Git blob, commit, attribution and CC BY-SA license pinned.
- [x] Original file metadata and 22 feature annotations source-inspected without copying bases.
- [x] Reuse DASHI.Codec.DNAFirstFormalism and DNACarrierFibre; no second base alphabet.
- [x] Reusable strict read-only Biopython parser: exact positions, join/order and reverse strand, circular topology, source and semantic digest.
- [x] Independent Git-blob/feature-location/qualifier-order parity checker implemented.
- [x] Golden Agda GenBankLocationFiniteCore source-written with coordinate reconstruction and strand involution.
- [x] Non-Golden adapter to DNA, contextual translation, situated protein, avian PNF, Wikidata repair/reopening owners.
- [x] Candidate-only source-reopenable ontology and protein annotation review worklist implemented.
- [x] Source-specific creator-file feature-index-8 -> Nimpf vestibular hypothesis crosswalk is source-written and requires full Git-blob parity before emitting candidate links.
- [x] Source inspection notes gene-like cacna1d source label is misc_feature, NOT one of two CDS.
- [x] Synthetic tests, read-only boundaries and canonical import roots updated.

## OPEN exact remaining gates

- [ ] GB02-REAL: execute Biopython parser and original-source parity checker on creator's exact Git blob 0578ad167666789fbfd3faa849a455c25097b90c.
- [ ] GB02-STRICT: check fuzzy/reverse-joined/exact interval malformed-case negative fixtures; avoid silent acceptance.
- [ ] GB03-KERNEL: compile Golden and non-Golden exact Agda owners on exact branch head; attach toolchain and 0 postulates/metas/termination escape.
- [ ] GB04-FULL: complete and test full-record semantic parse/serialize/parse roundtrip (only nested exact feature-location roundtrip now implemented).
- [ ] GB05-SOURCE: source-align 2020 transcript passages against original 22 feature annotations; no guessed edit provenance.
- [ ] GB06-PROTEIN: independently source-match accession, organism, isoform, reading frame, genetic code and context to original UniProt/NCBI; no blind translation of misc_feature label.
- [ ] GB07-ONTOLOGY: bind to native ITIR/SLR S29 interface, run native fixture-backed conformance and attribution/reopen checks; candidate-only JSON is not native acceptance.
- [ ] GB08-VERIFY: execute exact-head pytest, Agda and optional Lean mirror; inspect and reconcile parallel BH4 ontology PR #1454.
- [ ] GB08-DOCS: update final referee receipt and paper/roadmap acceptance ledger after kernel/tests run.

Priority: original same-object parser replay, then Golden kernel, then full-record semantic and ontology ABI.
No operational human or animal gene editing or delivery protocols in this lane.
