# Wikidata property-proposal deliberation: source and authority cut

**Formal owner:** `DASHI/Ontology/WikidataDeliberationGovernanceExact.agda`.
Imported by `DASHI/Ontology/WikidataWorkingGroupEverything.agda`; exercised by the focused working-group regression. Draft branch: kernel execution not yet receipted.

## Original prior art, original authors and mathematical ownership

- Marcin Roszkowski (2024), *Navigating change: an exploration of socio-epistemic process of extending Wikidata ontology with new properties*, *Journal of Documentation* 80(6):1291–1312. DOI **10.1108/JD-01-2024-0008**. The empirical three-phase account and analysis of community practices belong to Roszkowski.
- Roszkowski (2026), *“Done. Make Good Use of It.” Epistemic Practices Behind Wikidata's Ontology Evolution*, Wikimedia CEE Open Knowledge conference. The example P10322 `time in the pouch` is a source-historical specimen, **not** a new DASHI discovery.
- Wikidata contributors and community governance own historic property creation, rules and deliberations.
- DASHI owns the newly defined **conditional** governance interface and projection theorems. They are not claims by Roszkowski that formal proofs exist.
- Original JMD Lean finite-KB diagnostic and repair-review code and the original Ege Doğan/Peter Patel-Schneider disjointness method remain separately attributed. Rosario/IBM benchmark framing, climate/Nat migration and Wikidata change-repair implementation belong to their respective original researchers and repo source owners; these are **not** implied by the deliberation model.

## O/R/C/S/L/P/G/F

| Field | Obligation |
| --- | --- |
| O | DASHI is golden semantics; SLR owns native source/S29 persistence, ITIR projects source candidates, the community owns community revision/edit permission. |
| R | Separate source existence, exact byte-span authentication, actor authority, consensus, historical policy and age from the recorded event type. |
| C | Existing `EpistemicInquiryGovernance` / `WikidataDiagnosticGovernanceExact` reused; this leaf adds indexed `SourceVerifier`, `CommunityRule`, `ClosureAdmission`, independent support/counter-support. |
| S | `SourceAnchoredEvent` carries claimed revision, byte interval, digest, actor and clock time. Evidence verification remains an explicit predicate, not computed from the string. |
| L | `DeliberationContestationFibre` has independent support/counter-support Booleans, retaining both and neither separately. |
| P | A `ClosureAdmission` is conditional on all authenticating and community policy witnesses; it is **not** an edit mandate or ontology truth certificate. |
| G | The actual community decides creator authority, consensus and historical policy applicability. Automated checkers and AO cannot self-authorise. |
| F | Independent source, role, consensus, policy and temporal obligations are extractable from the admitted record; a negative witness to one blocks the whole closure. |

## Exact implemented lemmas

- `admissionRequiresCreatorAuthority`
- `admissionRequiresIndependentCreator`
- `admissionRequiresPolicySource`
- `admissionRequiresConsensus`
- `admissionRequiresPolicyVersion`
- `admissionRequiresExactSource`
- `noCreatorAuthorityBlocksClosure`
- `sameActorCreatorBlocksClosure`
- `missingPolicySourceBlocksClosure`
- `missingConsensusBlocksClosure`
- `missingSourceAuthenticationBlocksClosure`
- `formalCheckerDoesNotSelfAuthoriseCommunityRevision`: reuses original `WikidataDiagnosticGovernanceExact` owner rather than reproving authority.
- `sourceEvidenceDoesNotGrantAutomaticExternalEdit`: an explicit, uninhabited automatic-edit permission cannot be manufactured by source evidence.
- `bothObserved` / `neitherObserved` and the working-group regressions: support and counter-support never collapse into one approval count.

The closure type additionally demands a separately authenticated *historical-policy source* and a creator/proposer separation witness; neither is supplied by a checksum string or by the recorded decision actor's name. Theorems are **conditional interface laws**, not a kernel-verified historical consensus judgement, not an unconditional Wikidata policy assertion, and not formal verification of the Rust/Python adapters. In particular, `SourceVerifier.Authenticated` must be supplied by a separately trusted byte-reopening producer and `CommunityRule` must be grounded in the historically effective policy. Neither a property ID nor a user-provided checksum constructs these witnesses.

## Physical cross-repository consumer contract

- SLR PR **#76**: source revision seals and exact byte-span event anchors, canonical content reopen, scoped durable sidecar, existing S29 `OntologyDiagnostic` with evidence request, qualification and abstention (not an edit approval). Opt-in end-to-end PG regression needs a **disposable migrated database** with `SLR_DELIBERATION_PG_ACCEPTANCE=1`.
- ITIR-suite PR **#70**: generic pure `itir.governance.deliberation_assessment`, `itir.governance.deliberation_slr_handoff` (ISO timestamp to SLR exact epoch-second shape, caller-supplied seals/anchors, **unverified**), and `itir.governance.deliberation_consumer_link` (candidate-only joins for existing `ChangeReviewPacket`, `sl.wikidata_signal_review_bundle.v0_1`, climate/Nat, P2738/Ege-Peter and Rosario/hotspot).
- The ITIR packet ID and Rust serialized-packet digest are **not claimed equal**. They are different receipts over respective encodings; a witnessed same-object transport requires canonical field reconciliation and original source-backed anchor checking. The ITIR handoff records the precise Rust field grammar, not the independently verified source content.
- Peter/Ege violations and culprits, Rosario benchmarks, climate/Nat A–E classification, and ChangeReviewPacket `severity(after) <= severity(before)` remain **independent consumer obligations**, never paid by proof of proposal-history completeness.

## Acceptance state and remaining mathematical/empirical cut

1. Confirm exact-head **Agda kernel check**: `scripts/run_agda29_parallel_check.sh DASHI/Ontology/WikidataDeliberationGovernanceExact.agda`, then focused root and authoritative pinned track; only an executed receipt may promote them as checked.
2. Run `PYTHONPATH=itir-mcp/src python -m pytest itir-mcp/tests/test_epistemic_deliberation.py itir-mcp/tests/test_epistemic_deliberation_handoff.py -q` and `cargo test -p sensiblaw-pg-source-store epistemic_deliberation` with proper local dependencies.
3. Run opt-in **physical SLR PostgreSQL** test on disposable migrated DB, persist/reopen each exact event source, and verify S29 review row locking and replay.
4. Fetch **actual historical P10322 proposal revisions and the then-effective rule version**, verify author/time/event spans and community judgement. Fictional fixtures must not substitute for that corpus; current policy cannot be retroactively applied without the relevant version.
5. Materialize consumer-specific *source-verified* joins (real climate, real P2738, real hotspot, real candidate repair) under S30 knowledge-cut access controls; do not grant AO/SLR authority through shared references.
6. A strong cross-language same-object theorem would require a shared serialization/equivalence witness, replay invariance under source revision change, and a typed correspondence from the Rust/Python exact field objects to these abstract Agda predicates. The current bridge only names obligations and the exact shapes.

**Verification status:** source-written unexecuted Agda / Rust / Python, with an opt-in physical regression written but not run through the GitHub connector. No live edits, checker receipts or historical facts were synthesized.
