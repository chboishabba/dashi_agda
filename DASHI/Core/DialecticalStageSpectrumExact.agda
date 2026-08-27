module DASHI.Core.DialecticalStageSpectrumExact where

------------------------------------------------------------------------
-- DIALECTICAL STAGE SPECTRUM: HISTORICAL READING OF THE CANONICAL ATLAS
--
-- Historical provenance:
--   user-supplied DASHI origin/reconstruction notes (2025--2026), including
--   the recovered screen-splitting, probability-wave, ternary-refinement,
--   stage/basin, and 0--11 material discussed in the 2026-08-26/27 tranche.
--
-- Canonical repository authority:
--   DASHI.Foundations.StageAtlasZeroToEleven
--   DASHI.Foundations.StageValuationBundleAtlas
--
-- This module deliberately DOES NOT introduce a second 0--11 carrier or a
-- second canonical operational stage-role map.  The merged Foundations atlas
-- remains authoritative.  What is added here is a provenance-carrying
-- historical/interpretive reading over that already-existing carrier.
--
-- Important boundaries:
--   * canonical 0--11 atlas != M1--M10 motif classifier;
--   * historical reading != canonical operational stage role;
--   * stage index != human worth/rank or empirical psychometric scale;
--   * zero/neutral can retain the recovered "refine deeper" reading;
--   * stage 11 is not an invented motif M11.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Canonical

------------------------------------------------------------------------
-- Reuse the merged canonical carrier exactly.
------------------------------------------------------------------------

DialecticalStage : Set
DialecticalStage = Atlas.StageAtlasZeroToEleven

stage0 stage1 stage2 stage3 stage4 stage5 : DialecticalStage
stage6 stage7 stage8 stage9 stage10 stage11 : DialecticalStage
stage0 = Atlas.atlas-0
stage1 = Atlas.atlas-1
stage2 = Atlas.atlas-2
stage3 = Atlas.atlas-3
stage4 = Atlas.atlas-4
stage5 = Atlas.atlas-5
stage6 = Atlas.atlas-6
stage7 = Atlas.atlas-7
stage8 = Atlas.atlas-8
stage9 = Atlas.atlas-9
stage10 = Atlas.atlas-10
stage11 = Atlas.atlas-11

stageIndex : DialecticalStage → Nat
stageIndex = Atlas.toNat

stage10IndexIsTen : stageIndex stage10 ≡ 10
stage10IndexIsTen = refl

stage11IndexIsEleven : stageIndex stage11 ≡ 11
stage11IndexIsEleven = refl

------------------------------------------------------------------------
-- Historical/interpretive roles.  These are NOT a replacement for
-- Canonical.StageRole.  Their purpose is to retain versioned source meanings
-- without mutating the merged operational atlas.
------------------------------------------------------------------------

data HistoricalStageRole : Set where
  presemanticVoid
  primitivePosition
  polarRelation
  firstStructuredTriad
  expandedRelation
  hingeOrConjecture
  explicitTension
  firstEscapeBeyondStaticOpposition
  unresolvedOrRecursiveRemainder
  closureWithinCurrentFrame
  newAxisLift
  nestedPostLiftExtension
  : HistoricalStageRole

StageRole : Set
StageRole = HistoricalStageRole

historicalStageRole : DialecticalStage → HistoricalStageRole
historicalStageRole Atlas.atlas-0 = presemanticVoid
historicalStageRole Atlas.atlas-1 = primitivePosition
historicalStageRole Atlas.atlas-2 = polarRelation
historicalStageRole Atlas.atlas-3 = firstStructuredTriad
historicalStageRole Atlas.atlas-4 = expandedRelation
historicalStageRole Atlas.atlas-5 = hingeOrConjecture
historicalStageRole Atlas.atlas-6 = explicitTension
historicalStageRole Atlas.atlas-7 = firstEscapeBeyondStaticOpposition
historicalStageRole Atlas.atlas-8 = unresolvedOrRecursiveRemainder
historicalStageRole Atlas.atlas-9 = closureWithinCurrentFrame
historicalStageRole Atlas.atlas-10 = newAxisLift
historicalStageRole Atlas.atlas-11 = nestedPostLiftExtension

-- Backward-compatible name for existing PR consumers.  Its type makes clear
-- that this is the historical reading, not Canonical.stageRole.
stageRole : DialecticalStage → HistoricalStageRole
stageRole = historicalStageRole

------------------------------------------------------------------------
-- Explicit bridge to the already-merged canonical operational roles.
------------------------------------------------------------------------

canonicalStage5Role :
  Canonical.stageRole stage5 ≡ Canonical.decisionGateRole
canonicalStage5Role = refl

canonicalStage9Role :
  Canonical.stageRole stage9 ≡ Canonical.systemicClosureBarrierRole
canonicalStage9Role = refl

canonicalStage10Role :
  Canonical.stageRole stage10 ≡ Canonical.scalePromotedBundleRole
canonicalStage10Role = refl

canonicalStage11Role :
  Canonical.stageRole stage11 ≡ Canonical.crossScaleFreshUnitRole
canonicalStage11Role = refl

------------------------------------------------------------------------
-- Neutral/refinement semantics recovered from the historical ternary source.
------------------------------------------------------------------------

data TernaryResolution : Set where
  rejectHere refineDeeper acceptHere : TernaryResolution

resolutionFromSign : Nat → TernaryResolution
resolutionFromSign zero = refineDeeper
resolutionFromSign (suc zero) = acceptHere
resolutionFromSign (suc (suc _)) = rejectHere

zeroMeansRefine : resolutionFromSign 0 ≡ refineDeeper
zeroMeansRefine = refl

------------------------------------------------------------------------
-- Stage and motif remain separately named system roles.
------------------------------------------------------------------------

data SystemKind : Set where
  canonicalStageSystem operationalMotifSystem : SystemKind

differentSystemKinds :
  canonicalStageSystem ≡ operationalMotifSystem → ⊥
differentSystemKinds ()

------------------------------------------------------------------------
-- Provenance metadata.
------------------------------------------------------------------------

record StageProvenanceEntry : Set where
  constructor stage-provenance-entry
  field
    stage : DialecticalStage
    sourceClass : String
    reconstructedMeaning : String
    claimStatus : String

stage0Provenance : StageProvenanceEntry
stage0Provenance =
  stage-provenance-entry stage0
    "user-supplied DASHI origin/reconstruction notes"
    "void / presemantic / unresolved field"
    "historical reading over canonical atlas; not external scientific theorem"

stage5Provenance : StageProvenanceEntry
stage5Provenance =
  stage-provenance-entry stage5
    "user-supplied DASHI threshold/stage notes"
    "hinge / conjecture / premature-collapse boundary"
    "historical reading; canonical operational role is decisionGateRole"

stage9Provenance : StageProvenanceEntry
stage9Provenance =
  stage-provenance-entry stage9
    "user-supplied DASHI closure/dimension-jump notes"
    "closure within current representational frame"
    "historical reading; canonical operational role is systemicClosureBarrierRole"

stage10Provenance : StageProvenanceEntry
stage10Provenance =
  stage-provenance-entry stage10
    "user-supplied DASHI +1 / dimension-jump notes"
    "new-axis lift after closure"
    "historical reading; canonical operational role is scalePromotedBundleRole"

stage11Provenance : StageProvenanceEntry
stage11Provenance =
  stage-provenance-entry stage11
    "user-supplied DASHI 0-11 reconstruction notes"
    "nested/coalesced post-lift extension"
    "historical reading; canonical operational role is crossScaleFreshUnitRole"

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record DialecticalStageSpectrumBoundary : Set where
  constructor dialectical-stage-spectrum-boundary
  field
    secondStageCarrierIntroducedHere : Bool
    secondStageCarrierIntroducedHereIsFalse :
      secondStageCarrierIntroducedHere ≡ false
    historicalReadingReplacesCanonicalStageRole : Bool
    historicalReadingReplacesCanonicalStageRoleIsFalse :
      historicalReadingReplacesCanonicalStageRole ≡ false
    stageIsIntrinsicHumanRank : Bool
    stageIsIntrinsicHumanRankIsFalse : stageIsIntrinsicHumanRank ≡ false
    stageIndexIsEmpiricalPsychometricScale : Bool
    stageIndexIsEmpiricalPsychometricScaleIsFalse :
      stageIndexIsEmpiricalPsychometricScale ≡ false
    stageSpectrumEqualsMotifClassifier : Bool
    stageSpectrumEqualsMotifClassifierIsFalse :
      stageSpectrumEqualsMotifClassifier ≡ false
    stage11IsMotifM11 : Bool
    stage11IsMotifM11IsFalse : stage11IsMotifM11 ≡ false
    everyHistoricalNoteUsedExactlyThisGlossary : Bool
    everyHistoricalNoteUsedExactlyThisGlossaryIsFalse :
      everyHistoricalNoteUsedExactlyThisGlossary ≡ false

canonicalDialecticalStageSpectrumBoundary : DialecticalStageSpectrumBoundary
canonicalDialecticalStageSpectrumBoundary =
  dialectical-stage-spectrum-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
