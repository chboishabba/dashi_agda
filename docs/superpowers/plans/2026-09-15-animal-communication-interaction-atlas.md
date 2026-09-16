# Animal Communication / Interaction Atlas Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a species-agnostic formal communication/interaction core beneath the merged magpie atlas, representing multi-emitter scenes, sender/addressee/response turns, query-indexed latent adequacy, semantic evidence, and a lossless magpie adapter.

**Architecture:** Keep the generic core in five focused Agda owners. Scene observation owns participants/modalities/emitter candidates and source-association status; interaction owns sender/receiver/response/turn structure; latent owns independently reopenable fibres plus finite query-adequacy defects; semantic evidence owns the evidence ladder and intervention/intent firewalls; the magpie adapter embeds existing magpie owners without upgrading their authority. A focused static checker lands before production owners and is wired into the existing birdsong/Animalexic validation path.

**Tech Stack:** Agda, DASHI Core `QueryIndexedProjectionAdequacyExact`, existing Animalexic/magpie formal owners, bash static contracts.

**Spec:** `docs/superpowers/specs/2026-09-15-animal-communication-interaction-atlas-design.md`

## Global Constraints

- Do not rewrite or delete the merged magpie owners.
- Runtime source separation / CV / audiovisual association models are out of scope; only their formal receipt ABI is declared.
- Multiple simultaneous emitter candidates and overlapping events must remain representable without forced collapse.
- Addressee identity, receiver response, and interaction turn are first-class coordinates.
- Species detection, emitter association, functional/semantic inference, and intervention authority remain separate query-indexed consumers.
- Structural analogy across species must not transfer mechanism or semantics.
- Unknown identities/associations remain explicit and fail-closed.
- Source-written/static status, executable static GREEN, and Agda/kernel certification remain separate.

---

### Task 1: RED static contract and validation hook

**Files:**
- Create: `scripts/check_animal_communication_interaction_static.sh`
- Modify: `scripts/check_bioacoustic_fly_state_space.sh`

**Interfaces:**
- Consumes: spec-named production owner paths.
- Produces: a source-level RED contract requiring all five owners and key boundary symbols.

- [ ] **Step 1: Create the failing static contract** requiring:
  - `AnimalCommunicationSceneObservationExact.agda`
  - `AnimalCommunicationInteractionExact.agda`
  - `AnimalCommunicationLatentExact.agda`
  - `AnimalCommunicationSemanticEvidenceExact.agda`
  - `MagpieAnimalCommunicationAdapterExact.agda`
  and symbols including `AnimalCommunicationScene`, `EmitterCandidate`, `InteractionTurn`, `receiverResponse`, `scenePresenceCannotAssignEmitter`, `signalFormCannotDetermineAddressee`, `responsePredictionDoesNotCreateMeaning`, `crossSpeciesAnalogyDoesNotCreateSameMechanism`, and `magpieAdapterDoesNotPromoteSemantics`.
- [ ] **Step 2: Wire the checker** into `scripts/check_bioacoustic_fly_state_space.sh` after the magpie atlas checker.
- [ ] **Step 3: Verify RED** by confirming the checker references owner paths that do not yet exist. If shell execution is unavailable, record source-RED only and do not claim executed RED.
- [ ] **Step 4: Commit** with message `test: require generic animal communication core`.

### Task 2: Scene observation owner

**Files:**
- Create: `DASHI/Biology/AnimalCommunicationSceneObservationExact.agda`

**Interfaces:**
- Produces: `SignalModality`, `ParticipantIdentityStatus`, `EmitterCandidate`, `AnimalCommunicationScene`, `SourceAssociationReceipt`, `SceneObservationBoundary`, and runtime handoff fields.

- [ ] **Step 1: Implement modality and identity vocabularies** for acoustic, visual, locomotor, vibration, electric, chemical, tactile, multimodal, unresolved; species/individual/group/track/source-stream identity stay independent.
- [ ] **Step 2: Implement `EmitterCandidate`** carrying participant ref, source/event ref, species status, visual-track status, acoustic-stream status, cross-modal association status/residual, provenance, and decision status.
- [ ] **Step 3: Implement `AnimalCommunicationScene`** carrying scene/source/time/environment references, participant refs, emitter candidates, overlapping event refs, and receipt refs.
- [ ] **Step 4: Add finite evening-chorus witness** with two species present and one unresolved event such that species presence projection collides while emitter identity differs; derive `scenePresenceCannotAssignEmitter` through `QueryIndexedProjectionAdequacyExact`.
- [ ] **Step 5: Add boundaries**: loudest != unique sender; visual proximity != acoustic emitter; temporal overlap != interaction; classifier score != canonical truth.
- [ ] **Step 6: Commit** with message `feat: add generic multi-emitter communication scenes`.

### Task 3: Interaction-turn owner

**Files:**
- Create: `DASHI/Biology/AnimalCommunicationInteractionExact.agda`

**Interfaces:**
- Consumes: scene/event refs from Task 2.
- Produces: `ReceiverSetStatus`, `ReceiverResponse`, `InteractionTurn`, `InteractionRelation`, addressee/response nonfactorability witnesses.

- [ ] **Step 1: Implement receiver/addressee set status** supporting none observed, singleton candidate, multi-receiver candidate, unresolved.
- [ ] **Step 2: Implement `ReceiverResponse`** carrying response modality/type, interval, observation coverage, provenance and decision.
- [ ] **Step 3: Implement `InteractionTurn`** with sender, receivers, signal ref, pre-state, response ref, delta-time, next-turn ref, context and provenance.
- [ ] **Step 4: Add addressee collision**: same sender and signal form, different directed receiver contexts; derive `signalFormCannotDetermineAddressee`.
- [ ] **Step 5: Add response collision**: same signal/context projection, different receiver response; derive `signalContextCannotDetermineResponse`.
- [ ] **Step 6: Add boundaries**: no detected response != no response absent coverage; co-occurrence != addressee; followed-by != responded-to; response correlation != causal mechanism.
- [ ] **Step 7: Commit** with message `feat: add sender receiver response interaction turns`.

### Task 4: Generic latent / query adequacy owner

**Files:**
- Create: `DASHI/Biology/AnimalCommunicationLatentExact.agda`

**Interfaces:**
- Consumes: scene and interaction owners; `QueryIndexedProjectionAdequacyExact`.
- Produces: generic latent fibres, `CommunicationQuery`, consumer-relative adequacy defects, cross-species analogy boundary.

- [ ] **Step 1: Define independently reopenable fibres** for signal form, sender, receiver, interaction turn, response, function/semantic hypothesis, population/geography, individual realization, history/context, environment, recording provenance, physical measurement.
- [ ] **Step 2: Define queries** `speciesPresent`, `eventEmitter`, `eventAddressee`, `receiverResponseQuery`, `functionalClass`, `semanticClass`, `crossSpeciesStructuralAnalogy`.
- [ ] **Step 3: Add finite species-vs-emitter defect** showing a species-presence observer can be adequate for scene species presence while inadequate for event-emitter identity.
- [ ] **Step 4: Add emitter-vs-function defect** showing exact emitter identity can still be inadequate for functional/semantic class.
- [ ] **Step 5: Add cross-species analogy boundary** and symbol `crossSpeciesAnalogyDoesNotCreateSameMechanism` plus same-semantics false promotion boundary.
- [ ] **Step 6: Commit** with message `feat: add query-indexed animal communication latent core`.

### Task 5: Semantic/function evidence owner

**Files:**
- Create: `DASHI/Biology/AnimalCommunicationSemanticEvidenceExact.agda`

**Interfaces:**
- Consumes: generic observation/interaction refs.
- Produces: generic evidence ladder, payments, reopening policy, and intervention/intent firewalls.

- [ ] **Step 1: Define stages** signal observed -> recurrent form -> context association -> directed/addressee association -> predictive receiver response -> playback/intervention response -> supported functional/reference class -> candidate compositional semantics.
- [ ] **Step 2: Define `CommunicationEvidencePayment`** with repeated context, addressee evidence, natural receiver response, longitudinal history, playback/intervention evidence, published ethology, same-object identity, provenance, independent ancestry.
- [ ] **Step 3: Define generic promotion receipt** with current stage, human-readable gloss, decision, source genealogy, append-only/reopening flags.
- [ ] **Step 4: Add `responsePredictionDoesNotCreateMeaning` boundary** and block functional gloss -> intent, response -> promise/agreement, playback effect -> propositional meaning, model-generated signal -> known meaning.
- [ ] **Step 5: Add selective reopening policy** for segmentation, identity, sender/addressee assignment, response association, context, source genealogy and contradiction.
- [ ] **Step 6: Commit** with message `feat: add generic animal communication evidence ladder`.

### Task 6: Magpie adapter

**Files:**
- Create: `DASHI/Biology/MagpieAnimalCommunicationAdapterExact.agda`

**Interfaces:**
- Consumes: merged `MagpieVocalAtlasObservationExact`, `MagpieVocalAtlasLatentExact`, `MagpieSemanticPromotionExact` and generic owners.
- Produces: explicit adapter records/references demonstrating that existing magpie objects embed without semantic promotion.

- [ ] **Step 1: Define adapter mapping** from magpie event source/time/location/context/acoustic/motor/provenance fields into generic scene/event references while retaining unresolved receiver/addressee where not paid.
- [ ] **Step 2: Map magpie latent fibre names** into generic fibre families without identifying them definitionally across species.
- [ ] **Step 3: Map magpie semantic stage/evidence references** into generic evidence references only as source-bound adapter metadata; do not create stronger payment.
- [ ] **Step 4: Add `magpieAdapterDoesNotPromoteSemantics = true` boundary** and explicit false fields for adding receiver identity, interaction authority, or cross-species meaning.
- [ ] **Step 5: Commit** with message `feat: adapt magpie atlas to generic communication core`.

### Task 7: Validation roots, source audit, and PR

**Files:**
- Modify: `DASHI/Biology/BioacousticFlyStateSpaceValidation.agda`
- Modify: `DASHI/Biology/AnimalexicEverything.agda`
- Verify: `scripts/check_animal_communication_interaction_static.sh`
- Verify: `scripts/check_bioacoustic_fly_state_space.sh`

**Interfaces:**
- Consumes: all five owners.
- Produces: focused repository visibility and explicit certification status.

- [ ] **Step 1: Import all five owners** into both focused roots.
- [ ] **Step 2: Read back all production files** and verify every token required by the static contract is present.
- [ ] **Step 3: Run static/full checker if an executable checkout exists.** Otherwise report source-level contract satisfaction only.
- [ ] **Step 4: Check exact-head GitHub status/workflow runs.** Do not claim Agda/kernel GREEN without an exact-head successful receipt.
- [ ] **Step 5: Open a draft successor PR** from `agent/animal-communication-interaction-atlas` to `master`, documenting the formal/runtime boundary and merged #933 parentage.
- [ ] **Step 6: Commit any final validation-root edits** with message `test: wire generic animal communication validation`.
