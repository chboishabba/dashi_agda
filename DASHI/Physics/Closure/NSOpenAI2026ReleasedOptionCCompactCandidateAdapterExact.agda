module DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionCCompactCandidateAdapterExact where

------------------------------------------------------------------------
-- RELEASED C / NATIVE PORT OF ComparatorR3Theorem.option_C_of_compact_candidate
--
-- The released Lean theorem is an adapter, not the hard construction:
--
--   compact candidate properties
--      + force support/smoothness
--      + normalization of any comparator solution
--      + candidate exclusion
--   ------------------------------------------------
--      comparator option C witness
--
-- This owner ports that logical body directly onto the canonical DASHI
-- comparator witness type.  The remaining C reconstruction therefore lies
-- below this adapter: construct the compact candidate package and its
-- normalization/exclusion facts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalShapeExact as Shape
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalWitnessExact as Witness

record OptionCCompactCandidateAdapter
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Shape.ReleasedInitialFieldShape
    rescaledForce : Shape.ReleasedVectorHistoryShape

    initialSmooth :
      Canonical.SmoothSpatialVector S initial
    initialDivergenceFree :
      Canonical.DivergenceFreeSpatial S initial
    initialRapidDecay :
      Canonical.RapidSpatialDecay S initial

    forceSmooth :
      Canonical.SmoothForcingHistory S
        (Shape.releasedForcingToCanonical rescaledForce)
    forceRapidDecay :
      Canonical.RapidSpaceTimeDecay S
        (Shape.releasedForcingToCanonical rescaledForce)

    NormalizedCandidateSolution : Set₁

    normalizeComparatorSolution :
      Witness.ReleasedGlobalSolutionC
        S viscosity initial rescaledForce →
      NormalizedCandidateSolution

    compactCandidateExcludesGlobalSolution :
      NormalizedCandidateSolution → ⊥

open OptionCCompactCandidateAdapter public

optionCOfCompactCandidate :
  ∀ {S viscosity} →
  OptionCCompactCandidateAdapter S viscosity →
  Witness.ReleasedComparatorCWitness S viscosity
optionCOfCompactCandidate A =
  record
    { Witness.initial = initial A
    ; Witness.forcing = rescaledForce A
    ; Witness.initialSmooth = initialSmooth A
    ; Witness.initialDivergenceFree = initialDivergenceFree A
    ; Witness.initialRapidDecay = initialRapidDecay A
    ; Witness.forcingSmooth = forceSmooth A
    ; Witness.forcingRapidDecay = forceRapidDecay A
    ; Witness.noReleasedGlobalSolution =
        λ solution →
          compactCandidateExcludesGlobalSolution A
            (normalizeComparatorSolution A solution)
    }

releasedOptionCCompactCandidateAdapterBodyPorted : Bool
releasedOptionCCompactCandidateAdapterBodyPorted = true

releasedCComparatorLayerStillHardAnalyticCut : Bool
releasedCComparatorLayerStillHardAnalyticCut = false

releasedCCompactCandidateConstructionClosedHere : Bool
releasedCCompactCandidateConstructionClosedHere = false

releasedCNormalizationAndExclusionClosedHere : Bool
releasedCNormalizationAndExclusionClosedHere = false

clayPromotion : Bool
clayPromotion = false

releasedOptionCCompactCandidateAdapterBodyPortedIsTrue :
  releasedOptionCCompactCandidateAdapterBodyPorted ≡ true
releasedOptionCCompactCandidateAdapterBodyPortedIsTrue = refl
