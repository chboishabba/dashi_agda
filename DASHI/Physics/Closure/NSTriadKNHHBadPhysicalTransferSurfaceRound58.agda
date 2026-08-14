module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalTransferSurfaceRound58 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_) 

import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

record PhysicalDyadicThreeMechanismTransfer : Set where
  field
    parameter : Threshold.PositiveThreshold

    defectRate : Nat → ℚ
    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    inheritedCoefficient generated leakage : Nat → ℚ
    inheritedCoefficientNonnegative : ∀ q → 0ℚ ≤ inheritedCoefficient q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q

    ceiling alpha beta : ℚ
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
