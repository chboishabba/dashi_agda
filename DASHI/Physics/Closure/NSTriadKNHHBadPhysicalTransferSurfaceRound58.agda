module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalTransferSurfaceRound58 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_) 

import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

------------------------------------------------------------------------
-- Canonical localized source.
--
-- The transfer carrier below remains the analytic proof boundary, but its
-- component functions are now tied to one shell-localized Duhamel source.
-- This prevents an adapter from silently combining a defect from one source
-- with inherited/generated/leakage terms from another source.
------------------------------------------------------------------------

record LocalizedDuhamelSource : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate : Nat → ℚ
    inheritedCoefficient generated leakage : Nat → ℚ
    ceiling alpha beta : ℚ

open LocalizedDuhamelSource public

record PhysicalDyadicThreeMechanismTransfer : Set where
  field
    source : LocalizedDuhamelSource

    parameter : Threshold.PositiveThreshold
    defectRate : Nat → ℚ
    inheritedCoefficient generated leakage : Nat → ℚ
    ceiling alpha beta : ℚ

    -- These equalities are source identity, not new analytic assumptions.
    -- They make the legacy recurrence projections canonical views of `source`.
    sourceParameter : parameter ≡ LocalizedDuhamelSource.parameter source
    sourceDefectRate : defectRate ≡ LocalizedDuhamelSource.defectRate source
    sourceInheritedCoefficient : inheritedCoefficient ≡
      LocalizedDuhamelSource.inheritedCoefficient source
    sourceGenerated : generated ≡ LocalizedDuhamelSource.generated source
    sourceLeakage : leakage ≡ LocalizedDuhamelSource.leakage source
    sourceCeiling : ceiling ≡ LocalizedDuhamelSource.ceiling source
    sourceAlpha : alpha ≡ LocalizedDuhamelSource.alpha source
    sourceBeta : beta ≡ LocalizedDuhamelSource.beta source

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    inheritedCoefficientNonnegative : ∀ q → 0ℚ ≤ inheritedCoefficient q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q

    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ

    baseLinearInSelectedThreshold :
      defectRate zero ≤ Threshold.threshold parameter * ceiling

    coefficientTransfer : ∀ q →
      inheritedCoefficient (suc q) ≤ alpha * inheritedCoefficient q

    successorDecomposition : ∀ q →
      defectRate (suc q)
      ≡ Threshold.threshold parameter
          * Scale.inverseDyadicScale (suc q)
          * inheritedCoefficient (suc q)
        + generated q + leakage q

    generatedAndLeakageForcing : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Scale.inverseDyadicScale (suc q) * beta

    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open PhysicalDyadicThreeMechanismTransfer public
