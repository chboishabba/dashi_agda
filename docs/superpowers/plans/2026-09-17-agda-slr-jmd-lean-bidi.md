# Agda SLR JMD Lean BIDI Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the approved Agda golden contract connecting SLR production world-expansion to the JMD/Aristotle Lean Wikidata getter/elaborator/tester/prover with exact attribution and non-promotion boundaries.

**Architecture:** Add focused Agda owners for source attribution, world-observation/getter parity, Lean verification status, SLR↔Lean challenge resolution, and the P7d attachment/world-delta bridge. Strengthen the existing P7d.1 producer adapter owner so the Wikidata lane consumes a typed Lean verification/attachment receipt rather than only Boolean parity claims.

**Tech Stack:** Agda, existing DASHI attribution/Wikimedia/SensibLaw owners, existing SLR parity ABIs.

**Spec:** `docs/superpowers/specs/2026-09-17-agda-slr-jmd-lean-bidi-design.md`

## Global Constraints

- Agda is the golden semantic contract; SLR is production; JMD Lean is executable verifier/elaborator/prover.
- Reuse `AttributedSourceCore`, `AristotleNativeModelSourceExact`, `SLRWikimediaHandoffABIExact`, and existing SensibLaw world/frontier owners.
- The uploaded Aristotle archive is pinned by exact archive name and SHA-256; no DOI is supplied and none may be invented.
- Citation/source identity imports neither proof nor authority.
- Lean kernel success does not create external-world truth, legal authority, P7 admission, residual payment, or Agda proof.
- Do not introduce a new planner or parallel evidence ontology.
- No Agda/kernel GREEN may be claimed without a fresh observed kernel receipt.

---

### Task 1: Attribution envelope for the JMD/Aristotle Lean machine

**Files:**
- Create: `DASHI/Wikimedia/AristotleLeanMachineAttributionExact.agda`
- Create: `DASHI/Wikimedia/AristotleLeanMachineAttributionValidation.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`, `DASHI.Wikimedia.AristotleNativeModelSourceExact`.
- Produces: a source-bounded `AttributedSource`/atlas and exact archive SHA/name equalities, with no DOI and no proof/authority promotion.

- [ ] **Step 1: Write RED validation** importing the future owner and requiring the archive identity, SHA, no-DOI source role, citation-non-proof and citation-non-authority boundaries.
- [ ] **Step 2: Verify RED** by confirming the validation import target does not yet exist; record source-written RED if no Agda runtime is available.
- [ ] **Step 3: Implement the minimal attribution owner** using `mkNoDOISource` and the existing Aristotle source pin; use a digest URN as the canonical machine-readable source locator rather than inventing a web URL.
- [ ] **Step 4: Re-read validation against implementation** and keep kernel status unclaimed unless executable Agda is available.

### Task 2: Golden world-observation and getter-parity ABI

**Files:**
- Create: `DASHI/Wikimedia/LeanSlrWorldObservationBidiExact.agda`
- Create: `DASHI/Wikimedia/LeanSlrWorldObservationBidiValidation.agda`

**Interfaces:**
- Consumes: Task 1 attribution owner and `SLRWikimediaHandoffABIExact`.
- Produces: `WorldObservation`, `LeanGetterObservation`, `SlrGetterObservation`, normalization/projection functions, mismatch kinds, and a `GetterParityResidual` carrier.

- [ ] **Step 1: Write RED validation** requiring preservation of request/object/relation/source/revision/digest/value/provenance coordinates for both getter paths and a mismatch residual constructor.
- [ ] **Step 2: Verify RED** by confirming the production owner is absent.
- [ ] **Step 3: Implement minimal observation types and projection functions**; backend identity must not create semantic authority or claim truth.
- [ ] **Step 4: Add non-collapse firewalls** for getter-backend != observation semantics and observation disagreement != automatic truth judgment.

### Task 3: Lean verification/status ABI

**Files:**
- Create: `DASHI/Wikimedia/LeanWikidataVerificationExact.agda`
- Create: `DASHI/Wikimedia/LeanWikidataVerificationValidation.agda`

**Interfaces:**
- Consumes: Task 1 attribution and Task 2 world observation.
- Produces: independent status types for encoding, freshness, import, check, alignment, publication/report; `LeanVerificationReceipt`; import-faithfulness and kernel-receipt boundaries.

- [ ] **Step 1: Write RED validation** demonstrating legal combinations `Encoded + Passed + Stale`, `Current + NotRun`, and `KernelPassed + WrongObject`.
- [ ] **Step 2: Verify RED** by confirming the owner is absent.
- [ ] **Step 3: Implement typed statuses and verification receipt** retaining object/relation/source/revision/digest/proof-query/machine/report references.
- [ ] **Step 4: Add firewalls**: fetched != imported, imported != derived theorem, import-faithful != world truth, kernel passed != freshness, report generated != kernel passed, Lean proof != Agda proof.

### Task 4: SLR -> Lean challenge / Lean -> SLR resolution ABI

**Files:**
- Create: `DASHI/Wikimedia/SlrLeanChallengeBidiExact.agda`
- Create: `DASHI/Wikimedia/SlrLeanChallengeBidiValidation.agda`

**Interfaces:**
- Consumes: Tasks 2-3 and existing SensibLaw residual/frontier vocabulary.
- Produces: typed challenge kinds, `SLRLeanChallenge`, resolution kinds, `LeanChallengeResolution`, and candidate-only/non-refutation boundaries.

- [ ] **Step 1: Write RED validation** for counterexample, freshness, same-object, premise, type and relation-alignment challenges plus stale-import/wrong-object/statement-too-strong resolutions.
- [ ] **Step 2: Verify RED** by confirming the owner is absent.
- [ ] **Step 3: Implement minimal challenge/resolution records** retaining theorem/statement ref, candidate object/relation, source revisions, premise/conflicting-observation refs and alignment ref.
- [ ] **Step 4: Add firewalls**: counterexample candidate != formal refutation; challenge receipt != world truth; resolution != legal authority.

### Task 5: P7d attachment and observed-world-delta bridge

**Files:**
- Create: `DASHI/Wikimedia/MaboLeanSlrP7dBidiBridgeExact.agda`
- Create: `DASHI/Wikimedia/MaboLeanSlrP7dBidiBridgeValidation.agda`

**Interfaces:**
- Consumes: Tasks 2-4, `MaboResidualDrivenWorldExpansionStepExact`, `SensibLawResearchCompoundingLoopExact`, `SensibLawImmutableLegalResearchWorldExact`, `SensibLawMultiResidualProofFrontierExact`.
- Produces: same-object/relation attachment receipt, external-object-vs-representation identity boundary, observed world delta, freshness reopening, and the recurrence `frontier -> candidate -> admission -> observation -> verification/challenge -> delta -> posterior frontier`.

- [ ] **Step 1: Write RED validation** requiring predicted contraction != observed contraction; kernel passed != admitted; admitted != claim truth; representation identity != world identity; stale source reopens applicability without negating the historical theorem.
- [ ] **Step 2: Verify RED** by confirming the owner is absent.
- [ ] **Step 3: Implement bridge records** retaining exact source revision/digest, attachment/alignment, contracted/new/reopened residual refs, reasoning/identity/lineage/PNF delta refs, and candidate-only authority status.
- [ ] **Step 4: Reuse append-only world/frontier owners by typed fields/imports** rather than inventing another world store or scheduler.

### Task 6: Strengthen P7d.1 producer-adapter Agda parity

**Files:**
- Modify: `DASHI/Wikimedia/MaboResidualDrivenProducerAdaptersExact.agda`
- Modify: `DASHI/Wikimedia/MaboResidualDrivenProducerAdaptersValidation.agda`

**Interfaces:**
- Consumes: Tasks 1-5.
- Produces: typed Wikidata adapter parity surface retaining parent QID, target QID, property/relation, exact revision/digest, Lean verification ref and same-object/relation attachment status, while leaving residual class externally supplied.

- [ ] **Step 1: Extend validation first** to require the typed bridge and source/revision/attachment retention.
- [ ] **Step 2: Confirm the existing owner cannot satisfy the new validation as written** before changing it.
- [ ] **Step 3: Add the minimal typed parity records/functions** while preserving the existing Boolean boundary API for downstream compatibility.
- [ ] **Step 4: Add explicit firewalls**: Lean verification != ExpansionCandidate, producer identity != residual class, reachable Wikidata route != acquired/revisioned entity, verification != semantic authority/claim truth.

### Task 7: Source/authority audit and validation sweep

**Files:**
- Review all files from Tasks 1-6.

**Interfaces:**
- Consumes: all previous tasks.
- Produces: an auditable source-written tranche with no invented DOI/URL/authority/certification claims.

- [ ] **Step 1: Check every source-bearing owner** for exact archive/source identity, revision/digest, attribution relationship and non-promotion status.
- [ ] **Step 2: Check every runtime/kernel field** so source-written, runtime-observed and kernel-certified statuses remain distinct.
- [ ] **Step 3: Run available Agda validation commands if executable access exists; otherwise record the genuine execution blocker and do not claim GREEN.**
- [ ] **Step 4: Update #991 description only with exact source-written/verified status and current commit head; do not mark kernel GREEN without evidence.**