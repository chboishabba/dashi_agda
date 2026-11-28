module DASHI.Physics.YangMills.YMClayCMP102OriginalLastBCoefficientCeilingExact where

------------------------------------------------------------------------
-- Section38: the ACTUAL original omitted B endpoint has a
-- sharper coefficient source than the total B mass 10/57.
--
-- CMP109 already proves B coefficients decrease monotonically:
-- b_(n+1) <= b_n. The original singleton b_0=1/6 is already
-- owned by YMClayCMP102OriginalFactorialSingletonExact.
-- By induction EVERY actual original b_n <= 1/6. The same
-- source bounds A_n <=1/2. These are exact signed-independent
-- Bishop order facts, not new factorial carriers.
--
-- The omitted physical scalar term 2X*b_n X^n then has a
-- coefficient 2b_n <=1/3 (separate |X|^count power transport
-- remains the native geometrical order task).
-- No original SU(N) Wilson or mass-gap result follows.
-- Source written, pinned Agda 2.9 acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; 1ℚᵘ; _/_; *≤*)
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialSingletonExact as Singleton

originalBAtMostFirst : ∀ n →
  R._≤_ (CMP109.bCoefficient n) (CMP109.bCoefficient zero)
originalBAtMostFirst zero = P.≤-refl
originalBAtMostFirst (suc n) =
  P.≤-trans (CMP109.bStep n) (originalBAtMostFirst n)

originalAAtMostFirst : ∀ n →
  R._≤_ (CMP109.aCoefficient n) (CMP109.aCoefficient zero)
originalAAtMostFirst zero = P.≤-refl
originalAAtMostFirst (suc n) =
  P.≤-trans (CMP109.aStep n) (originalAAtMostFirst n)

originalBAtMostSixth : ∀ n →
  R._≤_ (CMP102.bCoefficient n) (R._⋆ (+ 1 / 6))
originalBAtMostSixth n =
  P.≤-respʳ-≃ Singleton.originalBSingleton
    (originalBAtMostFirst n)

originalAAtMostHalf : ∀ n →
  R._≤_ (CMP102.aCoefficient n) (R._⋆ (+ 1 / 2))
originalAAtMostHalf n =
  P.≤-respʳ-≃ Singleton.originalASingleton
    (originalAAtMostFirst n)

originalTwoNonnegative : R.NonNegative CMP102.two
originalTwoNonnegative =
  P.0≤x⇒nonNegx
    (P.p≤q⇒p⋆≤q⋆
      0ℚᵘ (+ 2 / 1)
      (Q.*≤* (Z.+≤+ z≤n)))

-- This controls the exact original B singleton coefficient of the
-- omitted n-th odd row, independently of the heavy Cauchy wings.
originalTwiceBAtMostThird : ∀ n →
  R._≤_
    (R._*_ CMP102.two (CMP102.bCoefficient n))
    (R._⋆ (+ 1 / 3))
originalTwiceBAtMostThird n =
  P.≤-respʳ-≃
    (let open P.ℝ-Solver
     in solve 0
       (Κ (+ 2 / 1) ⊗ Κ (+ 1 / 6)
         ⊜ Κ (+ 1 / 3))
       P.≃-refl)
    (P.*-monoˡ-≤-nonNeg
      (originalBAtMostSixth n)
      originalTwoNonnegative)
