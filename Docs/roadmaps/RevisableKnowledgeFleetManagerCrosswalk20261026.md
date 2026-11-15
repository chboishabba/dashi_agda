# Fleet / proof-search / revisable-knowledge integration — 2026-10-26

## Evidence and attribution

This is a proposed crosswalk by Johl Brown with OpenAI ChatGPT assistance, not a claim of implementation or verification of the external ITIR/SLR fleet manager. Inspected in-repository owners: `.autonomous-orchestrator/registry.json`, `.autonomous-orchestrator/parent_reports/paper7-root.json`, and `.codex_skill_work/orchestrator/SKILL.md`. Existing project skill says read canonical state, choose one bounded skill, execute, update state, repeat; paper7 reports contain lane claims, parent/child relationships, completion events, escalation/de-escalation rules and model selection. The separate fleet controller's code and contracts have not yet been retrieved; do not silently identify these with it.

## Three distinct states

- **Task execution**: queued / claimed / running / timed-out / returned / failed; a worker receipt says what process happened.
- **Formal result**: candidate / source-written / locally checked / kernel checked / counterexample / unresolved; a proof receipt says what theorem was established under what dependencies.
- **Epistemic admission**: source-root identified / acquisition reviewed / consumer-relevant / authority admitted / superseded / challenged; a knowledge receipt says which downstream claims can rely on the result.

No transition from task completion to theorem authority, or theorem authority to physical/institutional permission, is automatic.

## Candidate task schema (design only)

Each frontier task should carry:
- stable task ID, programme and consumer;
- exact residual theorem or experiment discriminator;
- dependency edges and source-root references;
- existing canonical owner / proposed module;
- required input artifact digests and authority;
- estimated cost, residual reduction and Pareto axes;
- claim and worker lane with lease/timeout and escalation rules;
- output receipt class (proof, counterexample, bounded negative search, source acquisition, physical experiment);
- verification, provenance, and selective invalidation edges.

## Integration max-cut

1. **Existing mathematical owner**: `DASHI/Core/ProofSearchExperimentalParetoCrossPollinationExact.agda` generates authority-separated proof and experiment routes.
2. **Existing scheduler**: `DASHI/Core/LiveSetParetoExperimentSchedulerExact.agda` compares only admitted, relevant experiments; never collapse axes into one arbitrary scalar.
3. **Existing revision**: `DASHI/Core/RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact.agda` determines which dependent claims to reopen.
4. **Existing fleet implementation**: `.autonomous-orchestrator/` and the orchestrator skill already demonstrate lane ownership, reports, bounded execution and escalation. Adapter must consume their actual receipt schema, not invent a replacement.
5. **External fleet / ITIR / SLR**: investigate canonical owner and current controller contracts before writing a bridge. Retired/legacy controllers must not be reintroduced.
6. **Exact failure cut**: observational collision in `RevisableObserverConsumerFactorizationExact.agda` becomes a *candidate* task: find a discriminating coordinate, repair the consumer or prove a scoped impossibility. Its existence alone does not create a runnable job or grant authority.

## Roadmap reprioritisation

- **F0** Locate authoritative fleet-manager implementation and latest PRs, including ITIR/SLR contracts; inventory task IDs, artifact references, receipts and retirement boundaries.
- **F1** Agda typecheck new consumer no-go and identify exact compiler environment.
- **F2** Define adapter from typed residuals to existing fleet task schema; test two-history collision as a bounded proof-search job.
- **F3** Return typed receipts to provenance and proof-admission gates; a successful worker exit must not count as kernel proof.
- **F4** Couple selective invalidation to incremental rescheduling; unaffected consumers and artifacts remain stable.
- **F5** Run cross-domain tests: source duplication, temporal order, D4h/NV invariance, rounding collisions, external evidence and ESD institutional permission.

## Completion criterion

A claim change should cause exactly its affected consumer frontier to be recomputed, yield provenance-preserving task receipts, admit only appropriately verified results, and leave unaffected knowledge untouched. This is the operational research-system goal; it is not yet proven or implemented.
