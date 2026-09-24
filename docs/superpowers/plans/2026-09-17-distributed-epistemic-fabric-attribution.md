# Distributed Epistemic Fabric + Attribution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalise the IPFS/OrbitDB/JMD/SOLFUNMEME + Agda/SLR/Lean/wiki-prover architecture with explicit source ownership, license observations, situated-access semantics and non-promotion firewalls.

**Architecture:** Reuse `AttributedSourceCore` and existing SensibLaw federated acquisition boundaries. Add separate source-atlas, plane-separation, proof-producer, and situated-access owners; keep execution/transport/source observations distinct from new DASHI theorems and from Johl Brown's discussion-origin architecture contributions.

**Tech Stack:** Agda, existing DASHI Core/Interop owners, GitHub source metadata.

**Spec:** `docs/superpowers/specs/2026-09-17-distributed-epistemic-fabric-attribution-design.md`

## Global Constraints

- Do not invent DOI/QID/license metadata.
- Public GitHub visibility does not imply an open-source license.
- JMD/meta-introspector repository observations, Johl Brown proposal-origin contributions, external technology claims and DASHI formal synthesis remain distinct.
- `content address != authority != proof != admission != projection != settlement != truth`.
- No Agda/kernel GREEN claim without an observed exact-head execution receipt.
- Reuse existing owners instead of creating replacement attribution, PNF, SLR, proof-search or federated-acquisition ontologies.

---

### Task 1: RED validation owner

**Files:**
- Create: `DASHI/Interop/DistributedEpistemicFabricValidation.agda`

**Interfaces:**
- Consumes: future production module names fixed by the approved spec.
- Produces: one focused validation root importing all four production owners.

- [ ] **Step 1: Create the failing validation import**

```agda
module DASHI.Interop.DistributedEpistemicFabricValidation where

import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact
import DASHI.Interop.DistributedEpistemicPlaneSeparationExact
import DASHI.Interop.DistributedProofProducerABIExact
import DASHI.Economics.SituatedInformationAccessFabricExact
```

- [ ] **Step 2: Verify RED by fetching every production path**

Expected: each future production path returns GitHub `404 Not Found` on this branch before implementation.

- [ ] **Step 3: Commit the RED owner**

Commit message: `test: add distributed epistemic fabric RED root`.

### Task 2: Attribution and license source atlas

**Files:**
- Create: `DASHI/Interop/DistributedEpistemicFabricSourceAtlasExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`.
- Produces: `ContributionOrigin`, `ContributionAttribution`, `RepositoryLicenseObservation`, JMD/external source records and canonical attribution firewalls.

- [ ] **Step 1: Encode contribution origins**

Use constructors for `jmdMetaIntrospectorOrigin`, `johlBrownOrigin`, `externalTechnologyOrigin`, and `dashiSynthesisOrigin`.

- [ ] **Step 2: Encode repository license observations**

Represent `mitLicenseObserved`, `agpl3LicenseObserved`, and `licenseNotObservedAtInspectedRoot` with inspected repository URL/ref text. Do not infer rights from missing files.

- [ ] **Step 3: Populate source atlas**

Use `mkNoDOISource` for repository/project sources. Include JMD/meta-introspector `erdfa-publish-rs`, `ipfs-dasl`, `mesh-sync-rs`, `zos-server`, `solfunmeme-dioxus`, `meta-meme`; include external OrbitDB/IPFS/BitTorrent/Solana architecture precedents as external technology coordinates; include a discussion-origin record for Johl Brown's architecture proposal without asserting legal title.

- [ ] **Step 4: Add firewalls**

Prove by empty types that attribution does not create legal title, license inference, semantic authority or theorem ownership transfer.

- [ ] **Step 5: Commit**

Commit message: `feat: add distributed fabric attribution atlas`.

### Task 3: Plane separation and event/projection architecture

**Files:**
- Create: `DASHI/Interop/DistributedEpistemicPlaneSeparationExact.agda`

**Interfaces:**
- Consumes: `SensibLawFederatedZOSAcquisitionExact` as the existing CID/federation authority boundary.
- Produces: typed planes, event lifecycle, projection roles and cross-plane non-collapse firewalls.

- [ ] **Step 1: Define eight plane constructors**

`artifactPlane`, `historyPlane`, `projectionPlane`, `situatedAccessPlane`, `contractPlane`, `proofSearchPlane`, `admissionPlane`, `settlementPlane`.

- [ ] **Step 2: Define canonical lifecycle event classes**

Include source observation, residual, proof request/return, promotion proposal/disposition, delivery/measurement and settlement events.

- [ ] **Step 3: Define technology-role witness record**

Record role strings for IPFS/DASL/eRDFa, OrbitDB, mesh-sync/ZOS, SLR/Postgres, Lean/wiki-prover, Agda/DASHI and SOLFUNMEME/Solana, all as bounded architecture roles rather than deployment claims.

- [ ] **Step 4: Add non-collapse firewalls**

Empty propositions for `CIDCreatesAuthority`, `ReplicatedEventCreatesTruth`, `ProjectionStatusCreatesKernelProof`, `KernelReceiptCreatesAdmission`, `SettlementCreatesTruth`, `PostgresProjectionIsGlobalTruth`.

- [ ] **Step 5: Commit**

Commit message: `feat: formalise distributed epistemic plane separation`.

### Task 4: Agda : SLR : Lean/wiki-prover proof-producer ABI

**Files:**
- Create: `DASHI/Interop/DistributedProofProducerABIExact.agda`

**Interfaces:**
- Consumes: existing Prelude; semantics align with SLR residual/re-entry and JMD Lean/Wikidata interop without replacing them.
- Produces: `InquiryAction`, `ProofProducerCapability`, `ProofObligation`, `ProofReceipt`, `ResidualDisposition`, canonical Think/Look/Review routing and no-promotion firewalls.

- [ ] **Step 1: Define action ownership**

`thinkAction`, `lookAction`, `reviewAction`; document that proof engines cannot substitute for acquisition or authority review.

- [ ] **Step 2: Define producer ABI records**

Bind exact world revision, obligation id, source bindings, checker identity/version, result, residual/dependency and artifact receipt.

- [ ] **Step 3: Define recurrence result**

A producer returns a receipt and/or residual disposition; SLR may re-enter unresolved obligations.

- [ ] **Step 4: Add firewalls**

Empty propositions for `ProofReceiptCreatesPromotion`, `CheckerSuccessCreatesPremiseAuthority`, `ThinkPaysMissingSource`, `ThinkPaysHumanReview`, `PaymentCreatesTruth`.

- [ ] **Step 5: Commit**

Commit message: `feat: add distributed proof producer ABI`.

### Task 5: Situated information access fabric

**Files:**
- Create: `DASHI/Economics/SituatedInformationAccessFabricExact.agda`

**Interfaces:**
- Consumes: Prelude only; conceptually feeds existing dashiTRADE/LES/game-theory consumers later.
- Produces: separately typed information object, access context, access path, access event, contract lifecycle and effective-access coordinates.

- [ ] **Step 1: Define access carrier**

Retain monetary cost, reachability, bandwidth, device/assistive compatibility, language, identity disclosure, surveillance burden, geographic gate, licence/reuse, machine/API access and temporal relevance.

- [ ] **Step 2: Define public/premium path relation**

Allow two access paths to share one underlying information identity while differing in capability/SLA/latency/capacity.

- [ ] **Step 3: Define contract lifecycle**

`quoted`, `authorized`, `provisioned`, `delivered`, `measured`, `settled` remain distinct states.

- [ ] **Step 4: Add firewalls**

Empty propositions for `ZeroPriceImpliesEffectiveAccess`, `PublicReachabilityImpliesEffectiveAccess`, `OpenLicenceImpliesEffectiveAccess`, `MachineClientImpliesCommercialRole`, `WriteAuthorizationImpliesEffectiveAccess`, `DetectionSLAImpliesEndToEndReaction`, `SettledContractCreatesTruth`.

- [ ] **Step 5: Commit**

Commit message: `feat: formalise situated information access fabric`.

### Task 6: Strengthen validation and source-audit

**Files:**
- Modify: `DASHI/Interop/DistributedEpistemicFabricValidation.agda`

**Interfaces:**
- Consumes: all four production owners.
- Produces: compile-time equalities for canonical booleans/license statuses and references to firewall theorems.

- [ ] **Step 1: Add equality checks**

Check representative canonical fields such as non-promoting attribution, `orbitDbCurrentlyDeployed = false`, `settlementCreatesTruth = false`, and public/premium same-object allowance.

- [ ] **Step 2: Source-audit every referenced import/path via GitHub**

Expected: every production file exists on the feature branch and every imported existing owner exists on base `master`.

- [ ] **Step 3: Do not claim compiler GREEN**

Record source-written/source-order-RED status unless an exact-head Agda execution receipt becomes available.

- [ ] **Step 4: Commit**

Commit message: `test: pin distributed epistemic fabric boundaries`.

### Task 7: Draft PR and report exact status

**Files:** none.

- [ ] **Step 1: Open a draft PR against `master`**

Summarize architecture, attribution boundaries, license observations and validation status.

- [ ] **Step 2: Report the remaining genuine blocker**

If no compiler execution surface is available, the only certification blocker is an exact-head Agda kernel/CI receipt; do not conflate this with source completeness.