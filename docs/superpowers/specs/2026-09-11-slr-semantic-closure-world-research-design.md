# SLR Semantic Closure World Research Design

## Goal

Turn the existing SLR/Wikimedia world pipeline into one recurrent, multilingual, multi-tranche world-growth loop. GWB, AU and Brexit feed the same `WorldResearchIteration` ABI. Wikipedia language editions, including Simple English Wikipedia, are peer evidence surfaces. Facts discovered on one surface may become available to consumers of another surface only as attributed propagated evidence; they never rewrite what the target surface originally said.

## Existing owners reused

- SensibLaw `sl.candidate_world_model.v0_1` remains the semantic/world carrier.
- Existing SLR GWB CandidateWorldModel, reviewed Wikimedia follow, identity contraction, source-role attachment and multilingual parser/PNF diagnostics remain producers.
- Existing Ibrahim/Wikimedia-first acquisition order remains the acquisition router.
- Existing Snowball/source-attribution boundaries remain authoritative for source identity, claim-relative primaryness and append-only evidence.
- Existing external-ontology router remains fallback-only after Wikimedia/consumer residuals.

No parallel terminal architecture is introduced.

## Semantic closure

For a Wikidata entity `q`, each Wikipedia surface has its own observed atom set `A(q, surface)`. A canonical semantic atom is admitted to shared closure only when it has a language-independent identity, initially one of:

1. `qid`: entity identity;
2. `wikidata-property`: `(subject_qid, property_pid, object_qid_or_literal_digest)`;
3. `wiki-link`: `(root_qid, related_qid)` from a paid Wikipedia/QID link weld;
4. `world-edge`: an already-paid CandidateWorldModel/QID relation with stable identifiers.

Surface-local lexical/PNF material without such a weld remains local residual evidence and is not propagated merely because it resembles another language.

The shared closure is append-only:

`W(q) = union of canonical atoms from admitted source surfaces and world graph evidence`.

For each surface `s`, the semantic gap is:

`G(q,s) = W(q) - A(q,s)`.

A propagated view carries every missing atom together with its original evidence coordinates. It explicitly records `target_surface_asserted=false`. Therefore propagation means "available to a consumer working in this language", not "the target article said this".

Contradictory atoms are not collapsed. They remain alternatives/conflicts until a downstream consumer resolves or abstains.

## Simple English Wikipedia

`simplewiki` is a peer surface, not assumed to be a subset, translation, or simplification of `enwiki`. Its facts contribute to closure under the same admission rules. Its missing facts are measured under the same gap function.

## World research recurrence

Each iteration consumes the current world plus source/tranche provenance and emits:

- canonical semantic atoms;
- per-surface observed atom sets;
- shared closure;
- per-surface semantic gaps;
- propagated evidence views;
- unresolved local PNF/semantic atoms;
- next acquisition obligations;
- tranche readiness/status.

The acquisition priority remains:

1. local/replay cache;
2. Wikidata Q/P graph;
3. Wikipedia editions including `simplewiki`;
4. Wikipedia category/related/current-first-link Ibrahim-style traversal;
5. DBpedia/YAGO/WordNet/Schema.org/Umbel only for declared residuals;
6. broader Snowball only for surviving consumer debt.

The recurrence is append-only:

`W_(t+1) = W_t union AdmissibleEvidence(Acquire(Gaps(W_t)))`.

## Tranche convergence

All three existing tranches use one readiness carrier:

- `gwb`: `world-ready`; current GWB CandidateWorldModel/Wikimedia graph is a paid input.
- `au`: `retained-source-ready`; 45 retained documents / 19,235 sentences are already execution-certified, but need projection into the generic world-research iteration before world closure claims are paid.
- `brexit`: `source-unpaid`; current structured intent fixture is not retained narrative/source text and cannot be promoted into a source world.

A tranche may be present in the joined ledger without being semantically ready.

## Translation compatibility boundary

Shared QID pays entity identity only. Cross-language PNF-role compatibility pays structural comparability only. Neither pays sentence alignment, translation equivalence, or claim-semantic equivalence. Semantic closure propagates only canonical atoms whose identity is paid independently of lexical translation.

## Success criteria

The first implementation is successful when it can:

- consume the existing GWB graph and multilingual artifacts;
- include `simplewiki` when a sitelink exists;
- construct canonical atom closure and per-surface gaps without rewriting target-source provenance;
- emit next acquisition obligations for missing/unknown surfaces or unresolved atoms;
- join GWB/AU/Brexit tranche states in one iteration ledger;
- preserve `candidate_only=true` and `semantic_promotion=false` throughout;
- expose formal firewalls for propagation-vs-source-assertion, same-QID-vs-semantic-equivalence, and tranche-readiness-vs-truth.
