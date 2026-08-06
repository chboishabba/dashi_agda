module DASHI.Biology.JFineCoarseRelativeScaleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Type jFine as the relative harmonic factor rather than the absolute fine
-- carrier.  The absolute 11-trit frequency scale factors as
--
--   jAbsoluteFine = jCoarse * jFine
--                 = 3^2 * 3^9 = 3^11.
--
-- The spatial refinement is reciprocal and is represented without division by
-- the exact spatial-frequency product identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

import DASHI.Physics.Common.FiniteRingScaleDualityExact as Scale

jCoarseFrequency : Nat
jCoarseFrequency = 9

jFineFrequency : Nat
jFineFrequency = 19683

jAbsoluteFineFrequency : Nat
jAbsoluteFineFrequency = 177147

-- Compatibility alias for earlier prose and clients.
jRelativeFrequency : Nat
jRelativeFrequency = jFineFrequency

jAbsoluteFineIsCoarseTimesJFine :
  jAbsoluteFineFrequency ≡ jCoarseFrequency * jFineFrequency
jAbsoluteFineIsCoarseTimesJFine = refl

jFineIsCoarseTimesRelative :
  jAbsoluteFineFrequency ≡ jCoarseFrequency * jRelativeFrequency
jFineIsCoarseTimesRelative = jAbsoluteFineIsCoarseTimesJFine

jFineIsThreePowerNine : jFineFrequency ≡ 19683
jFineIsThreePowerNine = refl

jRelativeIsThreePowerNine : jRelativeFrequency ≡ 19683
jRelativeIsThreePowerNine = refl

jNineStepSpatialFrequencyDuality : Scale.SpatialFrequencyScale
jNineStepSpatialFrequencyDuality = Scale.triadicNineStep

jNineStepDualProductIsOne :
  Scale.spatialNumerator jNineStepSpatialFrequencyDuality
    * Scale.frequencyNumerator jNineStepSpatialFrequencyDuality
  ≡ Scale.spatialDenominator jNineStepSpatialFrequencyDuality
    * Scale.frequencyDenominator jNineStepSpatialFrequencyDuality
jNineStepDualProductIsOne =
  Scale.dualProductIsOne jNineStepSpatialFrequencyDuality

record RelativeAddressFibre : Set where
  constructor relativeAddressFibre
  field
    coarseDepth : Nat
    absoluteFineDepth : Nat
    jFineDepth : Nat
    depthReconstruction : absoluteFineDepth ≡ coarseDepth + jFineDepth

open RelativeAddressFibre public

canonicalTwoToElevenFibre : RelativeAddressFibre
canonicalTwoToElevenFibre = relativeAddressFibre 2 11 9 refl

record JRelativeScaleBoundary : Set where
  constructor jRelativeScaleBoundary
  field
    jFineIsLiteralSelfDivision : Set
    jFineIsNotLiteralSelfDivision :
      jFineIsLiteralSelfDivision → Set

    jFineIsAbsoluteFineCarrier : Set
    jFineIsNotAbsoluteFineCarrier :
      jFineIsAbsoluteFineCarrier → Set

    relativeScaleConstructsContinuumWaveletTheory : Set
    relativeScaleDoesNotConstructContinuumWaveletTheory :
      relativeScaleConstructsContinuumWaveletTheory → Set

canonicalJRelativeScaleBoundary : JRelativeScaleBoundary
canonicalJRelativeScaleBoundary =
  jRelativeScaleBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
