module DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionDPeriodicCandidateAdapterExact where

------------------------------------------------------------------------
-- RELEASED D / NATIVE PORT OF ComparatorTheorem.option_D_of_candidate
--
-- The released periodic comparator proof has the same short adapter shape:
--
--   periodic candidate properties
--      + smooth/periodic/compact-time-supported rescaled force
--      + future-jet decay consequence
--      + normalization of any comparator solution
--      + candidate lifespan exclusion
--   ------------------------------------------------------------
--      comparator option D witness.
--
-- This owner ports that logical body.  The hard D work is therefore the
-- candidate construction / consequences and normalization-exclusion cone, not
-- the already-trivial comparator wrapper.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalShapeExact as Shape
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalWitnessExact as Witness

record OptionDPeriodicCandidateAdapter
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Shape.ReleasedInitialFieldShape
    rescaledForce : Shape.ReleasedVectorHistoryShape

    initialSmooth :
      Canonical.SmoothSpatialVector S initial
    initialDivergenceFree :
      Canonical.DivergenceFreeSpatial S initial
    initialPeriodic :
      Canonical.UnitPeriodicSpatialVector S initial

    forceSmooth :
      Canonical.SmoothForcingHistory S
        (Shape.releasedForcingToCanonical rescaledForce)
    forcePeriodic :
      Canonical.UnitPeriodicForcing S
        (Shape.releasedForcingToCanonical rescaledForce)
    forceRapidTimeDecay :
      Canonical.RapidTimeDecayAllForcingDerivatives S
        (Shape.releasedForcingToCanonical rescaledForce)

    NormalizedCandidateSolution : Set₁

    normalizeComparatorSolution :
      Witness.ReleasedGlobalSolutionD
        S viscosity initial rescaledForce →
      NormalizedCandidateSolution

    periodicCandidateExcludesGlobalSolution :
      NormalizedCandidateSolution → ⊥

open OptionDPeriodicCandidateAdapter public

optionDOfPeriodicCandidate :
  ∀ {S viscosity} →
  OptionDPeriodicCandidateAdapter S viscosity →
  Witness.ReleasedComparatorDWitness S viscosity
optionDOfPeriodicCandidate A =
  record
    { Witness.initial = initial A
    ; Witness.forcing = rescaledForce A
    ; Witness.initialSmooth = initialSmooth A
    ; Witness.initialDivergenceFree = initialDivergenceFree A
    ; Witness.initialPeriodic = initialPeriodic A
    ; Witness.forcingSmooth = forceSmooth A
    ; Witness.forcingPeriodic = forcePeriodic A
    ; Witness.forcingRapidTimeDecay = forceRapidTimeDecay A
    ; Witness.noReleasedGlobalSolution =
        λ solution →
          periodicCandidateExcludesGlobalSolution A
            (normalizeComparatorSolution A solution)
    }

releasedOptionDPeriodicCandidateAdapterBodyPorted : Bool
releasedOptionDPeriodicCandidateAdapterBodyPorted = true

releasedDComparatorLayerStillHardAnalyticCut : Bool
releasedDComparatorLayerStillHardAnalyticCut = false

releasedDPeriodicCandidateConstructionClosedHere : Bool
releasedDPeriodicCandidateConstructionClosedHere = false

releasedDNormalizationAndExclusionClosedHere : Bool
releasedDNormalizationAndExclusionClosedHere = false

clayPromotion : Bool
clayPromotion = false

releasedOptionDPeriodicCandidateAdapterBodyPortedIsTrue :
  releasedOptionDPeriodicCandidateAdapterBodyPorted ≡ true
releasedOptionDPeriodicCandidateAdapterBodyPortedIsTrue = refl
