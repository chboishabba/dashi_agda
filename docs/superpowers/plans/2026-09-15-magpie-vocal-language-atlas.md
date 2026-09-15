# Magpie Vocal Language Atlas Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a first formal magpie vocal-language atlas tranche that represents append-only situated vocal observations, separates latent semantic/geographic/group/individual/context/recording fibres, and blocks semantic or dialect promotion from acoustic similarity or regional predictability alone.

**Architecture:** Reuse the existing birdsong/Animalexic source, query-indexed adequacy, intersectional nonfactorability, and provenance machinery. Keep the first tranche formal-only: three small Agda owners plus a focused static contract and validation imports. Runtime ingestion remains in Animalexic PR #6 and is consumed only as candidate observation provenance.

**Tech Stack:** Agda, DASHI.Core proof/adequacy machinery, shell static contracts, GitHub PR #933.

**Spec:** `docs/superpowers/specs/2026-09-15-magpie-vocal-language-atlas-design.md`

## Global Constraints

- Preserve append-only evidence and reopening semantics.
- Unknown species/individual/group/location precision is first-class and must not be guessed.
- Latent similarity does not imply semantic identity.
- Region predictability does not imply dialect.
- Group sequence difference does not automatically imply regional dialect.
- Source titles do not pay exact location; video species labels do not pay individual identity.
- Raw digital amplitude does not imply calibrated SPL; visible motion does not imply biomechanical work.
- Semantic candidates do not create intervention authority or animal intent.
- Reuse existing DASHI/Animalexic governance machinery; do not add a new planner or scalar meaning score.
- Exact-head source, static, Agda-kernel and external empirical status remain separate.

---

### Task 1: Focused RED contract for the atlas tranche

**Files:**
- Create: `scripts/check_magpie_vocal_language_atlas_static.sh`
- Modify: `scripts/check_bioacoustic_fly_state_space.sh`

**Interfaces:**
- Consumes: agreed design spec and existing focused birdsong validation root.
- Produces: a static contract requiring the three atlas owners, the core firewalls, and their validation imports.

- [ ] **Step 1: Write the failing static contract**

Require these files and tokens:

```text
DASHI/Biology/MagpieVocalAtlasObservationExact.agda
DASHI/Biology/MagpieVocalAtlasLatentExact.agda
DASHI/Biology/MagpieSemanticPromotionExact.agda
VocalObservationLevel
LocationPrecision
MagpieVocalEvent
latentSimilarityDoesNotCreateMeaning
regionPredictabilityDoesNotCreateDialect
groupSyntaxDoesNotCreateRegionalDialect
semanticCandidateDoesNotCreateInterventionAuthority
modelPredictionDoesNotCreateAnimalIntent
```

Also require imports of all three owners in `DASHI/Biology/BioacousticFlyStateSpaceValidation.agda` and `DASHI/Biology/AnimalexicEverything.agda`.

- [ ] **Step 2: Observe RED**

Run the focused static script if a local execution environment is available. Expected result: failure because the three production owners do not yet exist. If no executable checkout is available, record RED as source-structural only and do not claim an executed failure.

- [ ] **Step 3: Wire the new static script into `check_bioacoustic_fly_state_space.sh`**

Add one invocation only; do not otherwise restructure the checker.

- [ ] **Step 4: Commit**

Commit message:

```text
test: require magpie vocal atlas owners
```

### Task 2: Append-only situated observation owner

**Files:**
- Create: `DASHI/Biology/MagpieVocalAtlasObservationExact.agda`

**Interfaces:**
- Consumes: `DASHI.Biology.BioacousticYouTubeSeedSourceExact`, existing `Prelude`, and source/provenance conventions.
- Produces: `VocalObservationLevel`, `LocationPrecision`, identity-status carriers, `MagpieVocalEvent`, observation hierarchy, and observation/provenance boundaries.

- [ ] **Step 1: Define the observation hierarchy**

Create:

```agda
data VocalObservationLevel : Set where
  segment call callSequence bout interactionEpisode groupRepertoire regionalRepertoire speciesWideAtlas : VocalObservationLevel
```

Retain lower-level identifiers explicitly in higher-level records rather than asserting an automatic promotion relation.

- [ ] **Step 2: Define precision/identity carriers**

Add finite enums for location precision and identity status, including an explicit unknown/unpaid state.

- [ ] **Step 3: Define `MagpieVocalEvent`**

The record must retain source/media/event IDs, start/end time references, species/individual/group identity status, location value/precision/provenance, region/context/environment labels, acoustic/motor/context provenance references, decision/status and receipt references. Use strings/booleans where this tranche only needs typed presence/boundary rather than a new numerical subsystem.

- [ ] **Step 4: Add source-bound canonical seed observations**

Represent the three YouTube seeds only as acquisition/source observations. Do not assign exact location, individual identity, semantic meaning or dialect status.

- [ ] **Step 5: Add observation boundary record**

Require true fields for:

```text
sourceTitleDoesNotCreateExactLocation
videoSpeciesLabelDoesNotCreateIndividualIdentity
rawAmplitudeDoesNotCreateCalibratedSPL
visibleMotionDoesNotCreateBiomechanicalWork
avSynchronyDoesNotCreateCausality
unknownIdentityRemainsFirstClass
appendOnlyObservationHistory
```

- [ ] **Step 6: Commit**

Commit message:

```text
feat: add magpie situated vocal observations
```

### Task 3: Hierarchical latent atlas and consumer-relative adequacy

**Files:**
- Create: `DASHI/Biology/MagpieVocalAtlasLatentExact.agda`

**Interfaces:**
- Consumes: `MagpieVocalAtlasObservationExact`, `DASHI.Core.QueryIndexedProjectionAdequacyExact`, `DASHI.Core.IntersectionalNonFactorability` if that is the current exact module name, and existing situated-fibre machinery.
- Produces: separated latent fibre tags, consumer queries, finite nonfactorability witnesses, and dialect/accent boundaries.

- [ ] **Step 1: Define separated latent fibres**

Create constructors representing:

```text
semanticCore
geographicRealisation
groupSyntax
individualVoice
situatedContext
environment
recordingProvenance
```

Do not define a single scalar meaning score.

- [ ] **Step 2: Define consumer-indexed atlas queries**

Include at least:

```text
acousticNearestNeighbour
sameCallFamily
sameGroupSequence
regionalRealisation
individualVoiceComparison
semanticFamily
provenanceAudit
```

- [ ] **Step 3: Prove acoustic-only inadequacy for semantic identity**

Construct two finite worlds with equal acoustic observation but different semantic-family answers. Use `Query.QueryAdequacyDefect` and `queryAdequacyDefectBlocksFactorisation` exactly as in the existing bioacoustic lag owner.

Produce:

```agda
latentSimilarityDoesNotCreateMeaning : ... → ⊥
```

- [ ] **Step 4: Prove region-predictability inadequacy for dialect status**

Construct two finite worlds exposing the same region-predictable surface while differing on whether the variation is biological dialect versus recording/context confound.

Produce:

```agda
regionPredictabilityDoesNotCreateDialect : ... → ⊥
```

- [ ] **Step 5: Add group/region non-collapse boundary**

Encode:

```agda
groupSyntaxDoesNotCreateRegionalDialect : Bool
```

as part of a boundary record alongside recording/channel/background confound blockers.

- [ ] **Step 6: Commit**

Commit message:

```text
feat: add magpie hierarchical latent atlas
```

### Task 4: Semantic promotion ladder

**Files:**
- Create: `DASHI/Biology/MagpieSemanticPromotionExact.agda`

**Interfaces:**
- Consumes: observation and latent atlas owners plus existing provenance/evidence conventions.
- Produces: staged semantic status, payment requirements, reopening rules, and intervention/intent firewalls.

- [ ] **Step 1: Define promotion stages**

Create a finite stage type matching the spec:

```text
observedEvent
candidateCluster
crossRecordingMotif
contextAssociatedFamily
crossGroupFunctionalFamily
candidateSemanticInvariant
validatedFunctionalReferentialClass
```

- [ ] **Step 2: Define semantic payment record**

Retain independent evidence coordinates for repeated production context, receiver response, longitudinal/group use, playback/intervention evidence, published ethology and source provenance. The record must permit unpaid coordinates; no field should silently imply another.

- [ ] **Step 3: Encode non-promotion boundaries**

Include explicit true fields/tokens:

```text
semanticCandidateDoesNotCreateInterventionAuthority
modelPredictionDoesNotCreateAnimalIntent
repeatedSelfPredictionDoesNotCreateIndependentCorroboration
classifierConfidenceDoesNotCreateSemanticTruth
sourceTitleDoesNotCreateSemanticTruth
```

- [ ] **Step 4: Encode reopening semantics**

Represent that later evidence may reopen segmentation, identity, location, call-family, geographic-realisation or semantic-payment dependencies without erasing earlier candidate history.

- [ ] **Step 5: Commit**

Commit message:

```text
feat: add magpie semantic promotion ladder
```

### Task 5: Validation/export wiring and GREEN verification

**Files:**
- Modify: `DASHI/Biology/BioacousticFlyStateSpaceValidation.agda`
- Modify: `DASHI/Biology/AnimalexicEverything.agda`
- Verify: `scripts/check_magpie_vocal_language_atlas_static.sh`
- Verify: `scripts/check_bioacoustic_fly_state_space.sh`

**Interfaces:**
- Consumes: all three new owners.
- Produces: focused validation/import coverage and exact-head verification evidence if available.

- [ ] **Step 1: Add imports**

Import/open all three new owners in the two focused roots, without reordering unrelated modules.

- [ ] **Step 2: Run focused static contract**

Expected: PASS if executable environment is available.

- [ ] **Step 3: Run top-level birdsong/fly static checker**

Expected: PASS if executable environment is available.

- [ ] **Step 4: Run the narrowest available Agda validation root**

Prefer the focused `BioacousticFlyStateSpaceValidation.agda` import root. If Agda is unavailable, do not infer kernel success from source presence.

- [ ] **Step 5: Inspect exact-head GitHub status/workflows**

Record exact head SHA and distinguish CodeRabbit/status checks from Agda/static certification.

- [ ] **Step 6: Commit any final wiring fixes**

Commit message:

```text
chore: wire magpie vocal atlas validation
```

- [ ] **Step 7: Update PR #933 description**

Summarize the observation owner, latent atlas, semantic promotion ladder, and the empirical/non-intervention boundary. Do not claim a decoded magpie dictionary.
