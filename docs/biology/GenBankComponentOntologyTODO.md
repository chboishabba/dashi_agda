# GenBank component ontology registry: exact acceptance gates (2026-11-03)

- [x] Reuse existing GenBank report and DNA codec instead of introducing
  a competing sequence parser or DNA representation.
- [x] Write a reusable INSDC feature-key taxonomy with distinct gene,
  CDS, regulatory, mobile, repeat, replication and miscellaneous classes.
- [x] Model mobile subtype from /mobile_element_type only on mobile_element.
- [x] Keep topology independent of source-annotated plasmid/chromosome;
  retain source qualifier conflicts and unknown contexts.
- [x] Preserve source feature order, coordinates, strand, compound order,
  original qualifier names and reopenable provenance.
- [x] Preserve unknown/legacy keys and deficient qualifiers as review holds.
- [x] Emit an ITIR/PNF-style read-only candidate graph; zero external edits.
- [x] Local tests of synthetic component/replicon classifications (16 passed).
- [ ] Execute new exact-head GitHub-branch Python tests in the actual checkout.
- [ ] Execute the classifier on the creator's exact source `.gb` files with
  independent Git blob identity and report a source-derived fixture.
- [ ] Kernel-check the Golden Agda component taxonomy and imports.
- [ ] Prove a full feature-location reverse-complement commuting square
  including circular origin-spanning joins; this component taxonomy alone
  makes no such claim.
- [ ] Validate and implement **native** ITIR/SLR S29 and/or external
  Sequence Ontology/Wikidata consumer ABI. Never guess external IDs.
- [ ] Source-match protein and feature labels only with organism, context,
  accession and version; review holds must not auto-promote to function.
- [ ] Reconcile the BH4 PR #1454 interop as a separate reusable consumer;
  no edits to ESD, archived/deprecated SensibLaw production surfaces.
