# Bridge invariants

1. The supplied Lean archive is the source artifact; the Agda bridge does not recreate or claim to kernel-check Lean proof terms.
2. Source matching includes the Aristotle request identity and pinned source hashes.
3. Accepted source-matched Lean theorem/checker results become scoped supporting evidence only.
4. A failed lookup/checker, source mismatch, missing edge, or absent proof contract is unresolved rather than contradicted **unless** a source-matched Lean theorem explicitly certifies the negative proposition (for example `P = false`). Certified falsity may contradict the corresponding expected-positive proposition; bare absence may not.
5. Native Wikidata `truthy` query semantics are not identified with DASHI epistemic truth.
6. Cross-ontology conflict requires explicit opposing evidence.
7. Identity/external-ID/sitelink/lexeme results remain candidate evidence outside their source hypotheses.
8. Diagnostics and pruning results feed `WikidataRepairProposal`; they do not acquire autonomous edit authority.
9. Certified redundant superclass removal is distinct from claiming that a superclass is semantically bad.
10. Abstract DASHI toy worlds are not represented as having been executed by James's concrete QID/P31/P279 kernel until an explicit content-addressed graph adapter exists.
11. All imported surfaces retain explicit truth/edit authority non-promotion.
