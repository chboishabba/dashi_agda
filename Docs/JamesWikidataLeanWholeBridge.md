# James Wikidata Lean whole bridge

## Source boundary

The source of truth for this integration is the complete Aristotle archive supplied for request `ae06ae06-2580-422a-8fc3-92aeaaca8762`, authored/reported by James Michael DuPont. The final archive contains 39 `RequestProject/*.lean` modules and 13,187 Lean source lines; this supersedes the earlier 36-module status graphic.

DASHI does **not** translate the entire Lean proof term graph into Agda or claim that Agda kernel-checks Lean. Instead it pins the exact source hashes, indexes every source module, records source-exact theorem/checker contracts, and maps those contracts into existing DASHI proof/epistemic boundaries.

## Existing DASHI surfaces reused

- `DASHI.Ontology.EpistemicTrit`: supported / unresolved / contradicted evidence state.
- `DASHI.Ontology.ContextualClaimComposition`: context-indexed claims and accumulated references.
- `DASHI.Ontology.WikidataEpistemicBridge`: native statement rank/qualifier/reference adapter, with rank deliberately distinct from truth.
- `DASHI.Interop.WikidataDerivationFibreBridge`: Wikidata-derived relation fibres.
- `DASHI.Interop.WikidataCandidateRoleBridge`: candidate identity/role evidence.
- `DASHI.Cognition.PNF.WikidataRepairProposal`: review-only ontology repair proposals.
- `DASHI.Core.AuthorityNonPromotionCore` and `CandidateOnlyCore`: explicit truth/edit/authority non-promotion.

## Bridge modules

`LeanWikidataSourceSnapshot.agda` pins archive/source identity. `LeanWikidataFullSourceManifest.agda` represents all 39 source modules and their DASHI anchors. `LeanWikidataTheoremSurfaceBridge.agda` records source-exact high-value theorem contracts across the development. `LeanWikidataWholeBridge.agda` provides generic source-matched receipt semantics.

Specialized bridge modules preserve distinctions in James's source rather than flattening the project into one generic certificate:

- `LeanWikidataAlignmentBridge`: mapped-ontology subclass/instance/disjointness preservation.
- `LeanWikidataDiagnosticsRepairBridge`: exact diagnostics plus semantics-preserving redundant-edge pruning, routed through review-only repair authority.
- `LeanWikidataDataModelBridge`: statement/rank/RDF query semantics, explicitly separated from epistemic truth.
- `LeanWikidataContextBridge`: sourced/reliable/temporal restrictions into `ScopedClaim`.
- `LeanWikidataIdentityBridge`: matching, sitelinks, external identifiers and lexeme denotation as candidate evidence.
- `LeanWikidataConstraintBridge`: property, statement, P1963, schema, path and mereology constraints.
- `LeanWikidataRdfExactnessBridge`: full-RDF injectivity, entailment soundness, P279/P31 exactness and executable-engine agreement.
- `LeanWikidataEverything`: aggregate root.

## Source-exact examples

The source contains theorem-backed executable class algebra:

- `Wikidata.KB.unionOk` -> `Wikidata.KB.isUnion_of_unionOk`
- `Wikidata.KB.interOk` -> `Wikidata.KB.isIntersection_of_interOk`
- `Wikidata.KB.isDisjointUnion_of_dunOk`

The worked artist fragment uses `Q483501` (artist), `Q1028181` (painter), and `Q1281618` (sculptor). The union may overlap; the example supplies the overlap witness.

The cross-ontology lane is source-native, not invented by the bridge: `RequestProject.Alignment` contains structure-preservation/reflection results including `Wikidata.Ontology.Alignment.subclassOf_iff` and `Wikidata.Ontology.Alignment.no_common_instance_of_disjoint`.

The diagnostics/repair lane includes `Wikidata.KB.errors_eq_nil_iff_valid` and `Wikidata.KB.warning_prunable`, while `RequestProject.Redundancy` proves that dropping a certified redundant subclass edge preserves validity and derived subclass/instance facts. DASHI therefore distinguishes `removeRedundantSuperclass` from `removeBadSuperclass`.

The RDF lane includes `Wikidata.Rdf.fullGraph_injective`, `entails_sound`, `entails_sub_iff`, `entails_inst_iff`, and `entails_iff_isSubclassOf`.

## Open-world and authority invariants

A source-matched accepted theorem/checker result is evidence supporting its scoped proposition. Source mismatch, failed checker, or missing theorem backing is `unresolved`, not automatically `contradicted`. Missing relations in an open-world source cannot manufacture negative evidence.

Imported Lean results carry neither global truth authority nor edit authority. Even theorem-backed redundancy witnesses produce review proposals rather than autonomous Wikidata edits.

## Provenance

`third_party/jmdupont_wikidata_lean/SOURCE_MANIFEST.tsv` records every supplied module's SHA-256, source-line count, declaration count, and direct imports. `LeanWikidataSourceSnapshot.agda` additionally pins the whole supplied archive SHA-256 and a combined RequestProject source hash.

The supplied archive contains no license file, so DASHI makes no relicensing claim.
