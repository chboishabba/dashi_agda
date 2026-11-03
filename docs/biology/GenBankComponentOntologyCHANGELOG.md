# GenBank component taxonomy / mobile element ontology — 2026-11-03

## Documents → TODO → Code → Changelog

- Source standard: INSDC DDBJ/ENA/GenBank Feature Table Definition **v11.4
  April 2026** (https://www.insdc.org/submitting-standards/feature-table/).
  Parser attribution: Cock et al., Biopython, *Bioinformatics* 2009,
  DOI 10.1093/bioinformatics/btp163. DNA and ontology proof owners are
  reused, not replaced; original GenBank source creators retain attribution.
- Added `docs/biology/GenBankComponentOntologyRegistry.md` contract and
  `docs/biology/GenBankComponentOntologyTODO.md` exact-scoped roadmap.
- Added `scripts/genbank_component_registry.py`. It accepts the existing
  `dashi.genbank.readonly.v1` source report or an original GenBank through
  the existing read-only parser and emits `dashi.genbank.component-registry.v1`
  plus optional `dashi.genbank.component-review.v1`. Feature and replicon
  classes stay separate. A mobile subtype requires an actual
  `mobile_element` key and valid `/mobile_element_type`; circular geometry
  does not imply a physical plasmid or chromosomal integration.
- Added `DASHI.Codec.GenBankComponentOntologyFiniteCore` with
  `{-# OPTIONS --safe #-}`, finite source-annotation, mobile-feature and
  replicon-context owners; no postulates, unsolved metas or terminating
  pragmas in authored source. Imported via Codec and Everything roots and
  existing Biology GenBank interpretation adapter.
- Added `tests/test_genbank_component_registry.py`, **16 local synthetic
  pytest cases passed**, including explicit mobile types, misc/repeat
  nonpromotion, independent topology/context, conflicting source qualifiers,
  exact compound/reverse locations, integrity/authority failures, and
  command-line input from an existing parser report.
- The committed Python implementation and test contents were re-read from
  GitHub and matched the locally executed sources by the same FNV-1a
  codepoint digest: script `462938bd`, test `10334c73`.
- Source-inspected original creator specimens in
  `docs/biology/data/ThoughtEmporiumComponentTaxonomyReadOnly.json`:
  22 annotated features (magnetoreception), 53 (penicillin yeast),
  20 (empty yeast backbone); all circular; none with source
  `mobile_element` key or `/plasmid` or `/chromosome` qualifiers.
  Original source bytes and real mobility/function are not asserted by
  this inspection.
- Added `tests/test_genbank_component_source_fixture.py` for
  nonpromotion, source SHA and documented feature-count regression.

### Verification ceiling

Source-writing and exact GitHub file readback are **not Agda kernel
acceptance**. The local 16-test suite was executed on source-equivalent
Python (confirmed by codepoint hash). The exact checked-out GitHub PR
pytest run, new fixture test execution, original-byte invocation of
this new taxonomy, and native ITIR/SLR recipient-ABI conformance remain
outstanding. The Golden core was not checked with an Agda executable.
The registry does not identify experimental function, select genetic
elements for engineering, output DNA bases, or change Wikidata.
