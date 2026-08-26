module DASHI.Core.DialecticalStageSpectrumExact where

------------------------------------------------------------------------
-- DIALECTICAL STAGE SPECTRUM: HISTORICAL / PROVENANCE-CARRYING OWNER
--
-- Source basis:
--   User-supplied DASHI origin/reconstruction notes, including the recovered
--   2025-2026 "nongin"/screen-splitting, probability-wave, ternary-refinement,
--   stage/basin, and 0--11 reconstruction material supplied in this thread.
--
-- This module is intentionally NOT sourced to Hegel, Freud, Lacan, p-adic
-- theory, dynamical systems, or the later DASHI motif classifier. Those may
-- motivate later bridges, but the 0--11 vocabulary is historical DASHI
-- provenance and must not be retroactively attributed to external literature.
--
-- Strong recovered source-level distinctions:
--   * the 0--11 stage spectrum is not the M1--M10 motif enum;
--   * zero/neutral can mean "current resolution insufficient: refine";
--   * higher stages are representational/meta-level roles, not ranks of people;
--   * stage 9 is closure within a frame; stage 10 is an explicit lift/new axis;
--   * stage 11 is kept as a post-lift/nested-extension role, not M11.
--
-- Intermediate stage names below are deliberately functional and conservative.
-- They preserve a total finite carrier without claiming that every historical
-- note used one immutable glossary for every index.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Canonical finite stage carrier.
------------------------------------------------------------------------

data DialecticalStage : Set where
  stage0 stage1 stage2 stage3 stage4 stage5
  stage6 stage7 stage8 stage9 stage10 stage11 : DialecticalStage

stageIndex : DialecticalStage → Nat
stageIndex stage0 = 0
stageIndex stage1 = 1
stageIndex stage2 = 2
stageIndex stage3 = 3
stageIndex stage4 = 4
stageIndex stage5 = 5
stageIndex stage6 = 6
stageIndex stage7 = 7
stageIndex stage8 = 8
stageIndex stage9 = 9
stageIndex stage10 = 10
stageIndex stage11 = 11

------------------------------------------------------------------------
-- Conservative semantic roles reconstructed from the supplied notes.
------------------------------------------------------------------------

data StageRole : Set where
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
  : StageRole

stageRole : DialecticalStage → StageRole
stageRole stage0 = presemanticVoid
stageRole stage1 = primitivePosition
stageRole stage2 = polarRelation
stageRole stage3 = firstStructuredTriad
stageRole stage4 = expandedRelation
stageRole stage5 = hingeOrConjecture
stageRole stage6 = explicitTension
stageRole stage7 = firstEscapeBeyondStaticOpposition
stageRole stage8 = unresolvedOrRecursiveRemainder
stageRole stage9 = closureWithinCurrentFrame
stageRole stage10 = newAxisLift
stageRole stage11 = nestedPostLiftExtension

------------------------------------------------------------------------
-- Neutral/refinement semantics recovered from the ternary source material.
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
-- Stage and motif remain separately named system roles.  We do not invent an
-- equality between their different carrier types merely to prove inequality.
------------------------------------------------------------------------

data SystemKind : Set where
  developmentalStageSystem operationalMotifSystem : SystemKind

differentSystemKinds :
  developmentalStageSystem ≡ operationalMotifSystem →
  Agda.Builtin.Equality._≡_ developmentalStageSystem developmentalStageSystem
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
    "historical reconstruction, not external scientific theorem"

stage5Provenance : StageProvenanceEntry
stage5Provenance =
  stage-provenance-entry stage5
    "user-supplied DASHI threshold/stage notes"
    "hinge / conjecture / premature-collapse boundary"
    "functional reconstruction; distinct from motif M5"

stage9Provenance : StageProvenanceEntry
stage9Provenance =
  stage-provenance-entry stage9
    "user-supplied DASHI closure/dimension-jump notes"
    "closure within current representational frame"
    "historical stage role; distinct from motif M9"

stage10Provenance : StageProvenanceEntry
stage10Provenance =
  stage-provenance-entry stage10
    "user-supplied DASHI +1 / dimension-jump notes"
    "new-axis lift after closure"
    "historical stage role; later motif M10 is a separate operational consumer"

stage11Provenance : StageProvenanceEntry
stage11Provenance =
  stage-provenance-entry stage11
    "user-supplied DASHI 0-11 reconstruction notes"
    "nested/coalesced post-lift extension"
    "kept fail-closed pending more exact June-note wording"

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record DialecticalStageSpectrumBoundary : Set where
  constructor dialectical-stage-spectrum-boundary
  field
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
