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
-- Type jFine/jCoarse as relative harmonic scale rather than literal
-- self-division.  For the balanced-ternary 11-trit fine carrier over the
-- 2-trit coarse carrier, the relative frequency multiplicity is 3^9.
-- Spatial refinement is reciprocal, represented division-free by the exact
-- spatial-frequency product identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

import DASHI.Physics.Common.FiniteRingScaleDualityExact as Scale

jCoarseFrequency : Nat
jCoarseFrequency = 9

jFineFrequency : Nat
jFineFrequency = 177147

jRelativeFrequency : Nat
jRelativeFrequency = 19683

jFineIsCoarseTimesRelative :
  jFineFrequency ≡ jCoarseFrequency * jRelativeFrequency
jFineIsCoarseTimesRelative = refl

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
    fineDepth : Nat
    relativeDepth : Nat
    depthReconstruction : fineDepth ≡ coarseDepth + relativeDepth

open RelativeAddressFibre public

canonicalTwoToElevenFibre : RelativeAddressFibre
canonicalTwoToElevenFibre = relativeAddressFibre 2 11 9 refl

record JRelativeScaleBoundary : Set where
  constructor jRelativeScaleBoundary
  field
    jRelativeIsLiteralSelfDivision : Set
    jRelativeIsNotLiteralSelfDivision :
      jRelativeIsLiteralSelfDivision → Set

    relativeScaleConstructsContinuumWaveletTheory : Set
    relativeScaleDoesNotConstructContinuumWaveletTheory :
      relativeScaleConstructsContinuumWaveletTheory → Set

canonicalJRelativeScaleBoundary : JRelativeScaleBoundary
canonicalJRelativeScaleBoundary =
  jRelativeScaleBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
