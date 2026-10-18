{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.StressEnergyEqualityCoreExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.StressEnergyWeldMathematicalCoreExact as Core

------------------------------------------------------------------------
-- PURE CROSS-SECTOR STRESS EQUALITY
--
-- Separate the physics equality from the legacy aggregation packaging.
-- This theorem shape says exactly what GRQFT needs physically on the overlap:
--
--   represented literal GR source = declared total QFT source.
--
-- QFTStressAggregation is a representation/totalization witness used by the
-- legacy SameStressEnergyWeld package, not a premise of the equality itself.
------------------------------------------------------------------------

record StressEnergyEqualityCore
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    sameStressEnergyOnOverlap :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.qftRegime U regime →
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime))
      ≡
      Weld.qftTotalStressShared U (Weld.coarseGrain U candidate regime)

open StressEnergyEqualityCore public

attachQFTAggregation :
  ∀ {U : Weld.UnifiedCandidate} →
  StressEnergyEqualityCore U →
  (∀ candidate →
    Weld.QFTStressAggregation U candidate
      (Weld.actualQFTSectorStressShared U candidate)
      (Weld.qftTotalStressShared U candidate)) →
  Core.StressEnergyWeldMathematicalCore U
attachQFTAggregation equality aggregation = record
  { Core.StressEnergyWeldMathematicalCore.qftStressAggregation =
      aggregation
  ; Core.StressEnergyWeldMathematicalCore.sameStressEnergyOnOverlap =
      sameStressEnergyOnOverlap equality
  }

stripAggregationPackaging :
  ∀ {U : Weld.UnifiedCandidate} →
  Core.StressEnergyWeldMathematicalCore U →
  StressEnergyEqualityCore U
stripAggregationPackaging core = record
  { StressEnergyEqualityCore.sameStressEnergyOnOverlap =
      Core.sameStressEnergyOnOverlap core
  }

qftAggregationIsPremiseOfCrossSectorEquality : Bool
qftAggregationIsPremiseOfCrossSectorEquality = false

qftAggregationIsPremiseOfCrossSectorEqualityIsFalse :
  qftAggregationIsPremiseOfCrossSectorEquality ≡ false
qftAggregationIsPremiseOfCrossSectorEqualityIsFalse = refl
