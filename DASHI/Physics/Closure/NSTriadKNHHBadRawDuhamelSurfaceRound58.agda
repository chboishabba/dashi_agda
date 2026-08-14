module DASHI.Physics.Closure.NSTriadKNHHBadRawDuhamelSurfaceRound58 where

------------------------------------------------------------------------
-- Lightweight raw A boundary.  This is the literal Duhamel datatype only;
-- no Holder, Luo Markov, or shell-barrier imports are pulled in here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

record PhysicalGeneralVariableDefectDuhamel : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate inherited generated leakage : Nat → ℚ
    alpha forcing : Nat → ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    inheritedNonnegative : ∀ q → 0ℚ ≤ inherited q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q

    successorDecomposition : ∀ q →
      defectRate (suc q) ≡ inherited q + generated q + leakage q

    inheritedTransfer : ∀ q →
      inherited q ≤ alpha q * Scale.half * defectRate q

    generatedLeakageTransfer : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Scale.inverseDyadicScale (suc q) * forcing q

open PhysicalGeneralVariableDefectDuhamel public
