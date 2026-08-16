# James / Aristotle Wikidata Lean whole bridge

This integration bridges the complete supplied Aristotle request
`ae06ae06-2580-422a-8fc3-92aeaaca8762` into existing DASHI ontology and
provenance machinery.

The final archive contains 39 `RequestProject/*.lean` modules and 13,187 source
lines. The archive, module hashes, theorem contracts, and integration targets are
pinned under `third_party/jmdupont_wikidata_lean/` and
`DASHI/Ontology/LeanWikidataFullSourceManifest.agda`.

## Division of labour

James's Lean development remains the proof authority for propositions internal
to the encoded Wikidata model. DASHI does not copy those propositions into Agda
as axioms. Instead, source-matched results enter DASHI as provenance-bearing,
scoped evidence and are constrained by the existing epistemic, candidate-only,
repair-review, derivation-fibre, and authority-nonpromotion boundaries.

The bridge therefore distinguishes:

- executable ontology semantics from epistemic authority;
- Wikidata's native `truthy` query projection from DASHI truth;
- identity evidence from identity promotion;
- redundancy from semantic wrongness;
- missing/open-world evidence from explicit negative evidence;
- RDF serialization, entailment soundness, entailment exactness, and executable
  engine agreement as separate guarantees.

## Certified falsity versus absence

The supplied source contains theorem-certified negative results such as:

- `Wikidata.ClassAlgebraExample.artistKB_not_dunOk`;
- `Wikidata.KB.brokenKB_not_valid`;
- `Wikidata.AlignmentExample.bad_links_alignOk_false`.

These exposed an important refinement to the original bridge. A bare checker
failure or missing edge remains `unresolved`, because open-world absence is not
negation. But a source-matched theorem explicitly proving `P = false` is positive
evidence for the negative proposition and may therefore project to
`contradicted` relative to an expected-positive claim `P`.

`LeanWikidataVerdictBridge.agda` formalises that distinction, and
`LeanWikidataSourceRegressionBridge.agda` exercises it on source-computed worked
KBs for class algebra, diagnostics, alignment, redundancy, and RDF.

## Existing DASHI content audit

The first attempted application to existing DASHI content found a genuine
representation boundary rather than a contradiction. The existing
`WikidataTypePressureMiniWorldExact` deliberately uses abstract constructors such
as `eventSeries`, `eventEdition`, and predicate-role evidence. It is not a
concrete QID/P31/P279 graph.

Consequently it would be unsound to claim that James's executable `KB` has
already checked that mini-world. `LeanWikidataExistingContentAudit.agda` makes
this explicit and requires a `ConcreteQidGraphAdapter` carrying a content hash
and the concrete P31/P279/disjointness references before a James-kernel execution
receipt can be accepted.

This is a strengthening: the bridge now tells us exactly which DASHI objects are
eligible for executable source checking and which first require a faithful
translation.

## Existing DASHI surfaces reused

- `DASHI.Ontology.EpistemicTrit`
- `DASHI.Ontology.ContextualClaimComposition`
- `DASHI.Ontology.WikidataEpistemicBridge`
- `DASHI.Interop.WikidataDerivationFibreBridge`
- `DASHI.Interop.WikidataCandidateRoleBridge`
- `DASHI.Cognition.PNF.WikidataRepairProposal`
- `DASHI.Core.AuthorityNonPromotionCore`
- `DASHI.Core.CandidateOnlyCore`

Specialized bridges preserve distinctions in James's source rather than
flattening the project into one generic certificate: alignment, diagnostics and
repair, data/rank semantics, provenance/temporal context, identity/lexical
evidence, constraints, and RDF exactness each have their own integration module.
`LeanWikidataEverything.agda` is the aggregate root.

## Source-exact examples

The source contains theorem-backed executable class algebra:

- `Wikidata.KB.unionOk` -> `Wikidata.KB.isUnion_of_unionOk`
- `Wikidata.KB.interOk` -> `Wikidata.KB.isIntersection_of_interOk`
- `Wikidata.KB.isDisjointUnion_of_dunOk`

The worked artist fragment uses `Q483501` (artist), `Q1028181` (painter), and
`Q1281618` (sculptor). Its union is accepted, while disjoint-union is explicitly
rejected because the fragment contains overlapping membership.

The source-computed regression bridge additionally pins diagnostic invalidity,
cycle/disjointness witnesses, valid redundancy/pruning examples, rejected bad
alignment, and the RDF `Q42 isInstanceOf Q35120` worked computation.

## Executable source audit

`third_party/jmdupont_wikidata_lean/SOURCE_MANIFEST.tsv` pins every supplied Lean
module. `BRIDGE_CONTRACTS.tsv` pins the currently high-value theorem contracts,
including both general semantic theorems and source-computed regression results.

`scripts/audit_james_wikidata_bridge.py` accepts an extracted `RequestProject`
directory and verifies:

1. all 39 expected modules are present and no unpinned module appears;
2. each source file matches its pinned SHA-256 and line count;
3. every bridge theorem contract names a declaration that actually exists in
   the corresponding source module.

This is intentionally source verification, not Lean kernel verification. A local
Lean build remains the proof-checking step for James's source, while the normal
Agda 2.9 pass remains the proof-checking step for DASHI.

## Authority invariants

Imported Lean results carry neither global truth authority nor edit authority.
Even theorem-backed redundancy witnesses produce review proposals rather than
autonomous Wikidata edits. Native Wikidata `truthy` semantics remain a query/data
projection rather than DASHI epistemic truth, and identity/alignment evidence is
not automatically promoted beyond its source hypotheses.

## Next concrete frontier

The next high-value work is not another generic wrapper. It is to construct a
content-addressed `ConcreteQidGraphAdapter` for a real DASHI/Wikidata fragment,
run James's exact P31/P279/diagnostic/RDF machinery on that graph, and feed the
result back through the verdict and repair lanes. That is where the imported
kernel can begin proving, refuting, or refining existing concrete DASHI ontology
claims rather than only supplying interoperability structure.

## Provenance

The supplied archive contains no license file, so DASHI records source hashes and
attribution but makes no relicensing claim.
