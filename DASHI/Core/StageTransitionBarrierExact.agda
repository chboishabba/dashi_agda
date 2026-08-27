module DASHI.Core.StageTransitionBarrierExact where

------------------------------------------------------------------------
-- STAGE-TRANSITION BARRIERS
--
-- Source basis:
--   User-supplied DASHI reconstruction notes describe levels as metastable
--   basins rather than ranks: a state can stabilise, oscillate, regress, or be
--   unable to move upward because the distinction required for the next move is
--   unavailable in the current representational frame.
--
-- Repo reuse:
--   * DASHI.Core.AdmissibleReachability owns proof-bearing finite reachability;
--   * DASHI.Reasoning.AttractorAlignedBranchSelectionExact owns desired,
--     blocked and trap basins;
--   * DASHI.Core.LevelIndexedProofObligationHyperformalismExact owns the
--     rechart-to-richer-level pattern when applicability lies outside the
--     current comparison scope.
--
-- This file introduces no second reachability relation and no second basin
-- calculus.  It packages barrier witnesses over those existing surfaces.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Level
import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Basin

------------------------------------------------------------------------
-- Barrier taxonomy.
------------------------------------------------------------------------

data StageBarrierKind : Set where
  representationalBarrier
  admissibilityBarrier
  trapBasinBarrier
  unresolvedResidualBarrier
  : StageBarrierKind

------------------------------------------------------------------------
-- Reachability-level stuckness: no admissible finite trace to a declared
-- target under the current action vocabulary.
------------------------------------------------------------------------

record UnreachableUnderCurrentVocabulary
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    (current target : State) : Set where
  constructor unreachable-under-current-vocabulary
  field
    noCurrentPath : Reach.Reachable system current target → ⊥

open UnreachableUnderCurrentVocabulary public

record ReopenedByRicherVocabulary
    {State Action₀ Action₁ : Set}
    (system₀ : Dependency.DependentActionSystem State Action₀)
    (system₁ : Dependency.DependentActionSystem State Action₁)
    (current target : State) : Set where
  constructor reopened-by-richer-vocabulary
  field
    blockedBefore : UnreachableUnderCurrentVocabulary system₀ current target
    reachableAfter : Reach.Reachable system₁ current target

open ReopenedByRicherVocabulary public

------------------------------------------------------------------------
-- Representational barrier: reuse the existing level-aware decision witness.
------------------------------------------------------------------------

currentEvidenceCanRequireRechart :
  Level.fineDecision Level.currentlyOutOfScope
  ≡ Level.rechartBeforeDecision
currentEvidenceCanRequireRechart = refl

sameFlatEvidenceCanHideRechartNeed :
  Level.flattenEvidence Level.currentlyApplicable
  ≡ Level.flattenEvidence Level.currentlyOutOfScope
sameFlatEvidenceCanHideRechartNeed =
  Level.flattenCollision

richerLevelCanReopenSameClaim :
  Level.ObligationLevelTransport
    Level.positiveOutOfScope
    Level.positiveReopenedAtNextLevel
richerLevelCanReopenSameClaim =
  Level.scopeToNextLevelTransport

------------------------------------------------------------------------
-- Attractor/basin bridge: "more branches" is not the same as escape.
------------------------------------------------------------------------

trapLookingBranchActuallyReachesTrapBasin :
  Basin.reachableBasin Basin.attractiveDeadEnd ≡ Basin.trapBasin
trapLookingBranchActuallyReachesTrapBasin = refl

moreNominalOptionsCanStillAddTrapStructure :
  Basin.AdverseMarginalWitness
moreNominalOptionsCanStillAddTrapStructure =
  Basin.moreOptionsCanWorsenReachableStructure

------------------------------------------------------------------------
-- Generic stuckness package.
------------------------------------------------------------------------

record StageBarrierWitness : Set₁ where
  constructor stage-barrier-witness
  field
    State Action : Set
    system : Dependency.DependentActionSystem State Action
    current target : State
    kind : StageBarrierKind
    noPath : Reach.Reachable system current target → ⊥

open StageBarrierWitness public

record StageTransitionBarrierBoundary : Set where
  constructor stage-transition-barrier-boundary
  field
    higherStageMeansHigherHumanWorth : Bool
    higherStageMeansHigherHumanWorthIsFalse :
      higherStageMeansHigherHumanWorth ≡ false
    moreOptionsGuaranteeEscape : Bool
    moreOptionsGuaranteeEscapeIsFalse :
      moreOptionsGuaranteeEscape ≡ false
    currentFailureImpliesPermanentImpossibility : Bool
    currentFailureImpliesPermanentImpossibilityIsFalse :
      currentFailureImpliesPermanentImpossibility ≡ false
    richerVocabularyMayReopenTransition : Bool
    richerVocabularyMayReopenTransitionIsTrue :
      richerVocabularyMayReopenTransition ≡ true

canonicalStageTransitionBarrierBoundary : StageTransitionBarrierBoundary
canonicalStageTransitionBarrierBoundary =
  stage-transition-barrier-boundary
    false refl
    false refl
    false refl
    true refl
