module DASHI.Moonshine.GoldenRatioBalancedFRACTRANReciprocalSquareConvergenceExact where

------------------------------------------------------------------------
-- 1/q_n^2 -> 0 ON THE VENDORED BISHOP CARRIER
--
-- Reuse the exact denominator lower bound q_n >= n+1 and the same rational
-- order/embedding pattern already used by the Bishop Basel owner.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP

import ExtraProperties as Extra
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANDenominatorGrowthExact as Growth

------------------------------------------------------------------------
-- 1. Write the denominator definitionally as a successor, so NonZero is
--    available to the unnormalised rational constructor.
------------------------------------------------------------------------

denominatorPred : Nat → Nat
denominatorPred n = Ratio.loPred (Ratio.iteratePositiveMacro n)

denominatorNat : Nat → Nat
denominatorNat n = suc (denominatorPred n)

denominatorAgrees :
  (n : Nat) → denominatorNat n ≡ Ratio.positiveLo (Ratio.iteratePositiveMacro n)
denominatorAgrees n = refl

reciprocalSquareRational : Nat → ℚᵘ
reciprocalSquareRational n =
  + 1 / (denominatorNat n * denominatorNat n)

reciprocalSquareBishop : Nat → BishopReal.ℝ
reciprocalSquareBishop n = BishopReal._⋆ (reciprocalSquareRational n)

------------------------------------------------------------------------
-- 2. Elementary denominator comparison.
------------------------------------------------------------------------

oneLeDenominator : (n : Nat) → 1 NatP.≤ denominatorNat n
oneLeDenominator n = NatP.0<⇒1≤n NatP.0<1+n

denominatorLeSquare :
  (n : Nat) → denominatorNat n NatP.≤ denominatorNat n * denominatorNat n
denominatorLeSquare n =
  NatP.≤-trans
    (NatP.*-identityʳ (denominatorNat n) NatP.≡⇒≤)
    (NatP.*-monoʳ-≤ (denominatorNat n) (oneLeDenominator n))

-- At any sequence index n >= k, the squared denominator is at least k.
precisionBoundToDenominatorSquare :
  (k n : Nat) →
  k NatP.≤ n →
  k NatP.≤ denominatorNat n * denominatorNat n
precisionBoundToDenominatorSquare k n k≤n =
  NatP.≤-trans
    k≤n
    (NatP.≤-trans
      (NatP.n≤1+n n)
      (NatP.≤-trans
        (Growth.linearDenominatorLowerBound n)
        (denominatorLeSquare n)))

------------------------------------------------------------------------
-- 3. Positivity/absolute value and Bishop convergence.
------------------------------------------------------------------------

reciprocalSquareNonnegative :
  (n : Nat) → BishopReal.NonNegative (reciprocalSquareBishop n)
reciprocalSquareNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (reciprocalSquareRational n)
      (ℚP.nonNegative⁻¹ (reciprocalSquareRational n)))

absoluteReciprocalSquare :
  (n : Nat) →
  BishopReal._≃_
    (BishopReal.∣ reciprocalSquareBishop n ∣)
    (reciprocalSquareBishop n)
absoluteReciprocalSquare n =
  BishopP.nonNegx⇒∣x∣≃x (reciprocalSquareNonnegative n)

reciprocalSquareSequenceConvergesZero :
  BishopSequence._ConvergesTo_
    reciprocalSquareBishop BishopReal.0ℝ
reciprocalSquareSequenceConvergesZero =
  BishopSequence.con* λ {(suc k-1) →
    k-1 , λ {(suc n-1) n≥k →
      let
        k = suc k-1
        n = suc n-1
        denominatorOrder :
          k NatP.≤ denominatorNat n * denominatorNat n
        denominatorOrder = precisionBoundToDenominatorSquare k n n≥k

        rationalOrder :
          reciprocalSquareRational n ℚ.≤ (+ 1 / k)
        rationalOrder =
          Extra.q≤r⇒+p/r≤+p/q
            1 k
            (denominatorNat n * denominatorNat n)
            denominatorOrder

        embeddedOrder :
          BishopReal._≤_
            (reciprocalSquareBishop n)
            (BishopReal._⋆ (+ 1 / k))
        embeddedOrder =
          BishopP.p≤q⇒p⋆≤q⋆
            (reciprocalSquareRational n)
            (+ 1 / k)
            rationalOrder
      in
      BishopP.≤-respˡ-≃
        (BishopP.≃-trans
          (BishopP.∣-∣-cong
            (BishopP.+-identityʳ (reciprocalSquareBishop n)))
          (absoluteReciprocalSquare n))
        embeddedOrder }}

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

record ReciprocalSquareConvergenceFrontier : Set where
  constructor reciprocal-square-convergence-frontier
  field
    denominatorSuccessorCarrierExact : Agda.Builtin.Bool.Bool
    denominatorDominatesIndexExact : Agda.Builtin.Bool.Bool
    reciprocalSquareConvergesZeroOnBishop : Agda.Builtin.Bool.Bool

canonicalReciprocalSquareConvergenceFrontier :
  ReciprocalSquareConvergenceFrontier
canonicalReciprocalSquareConvergenceFrontier =
  reciprocal-square-convergence-frontier
    Agda.Builtin.Bool.true Agda.Builtin.Bool.true Agda.Builtin.Bool.true
