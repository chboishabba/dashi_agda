module DASHI.Foundations.BishopNegativeExponentialQuarticBracketExact where

------------------------------------------------------------------------
-- LOW-ORDER BRACKETS FOR THE CONCRETE NEGATIVE EXPONENTIAL
--
-- On 0 <= x <= 1 the generic alternating interlacing instance gives
--
--   1-x <= exp(-x)
--   exp(-x) <= 1-x+x^2/2
--   exp(-x) <= 1-x+x^2/2-x^3/6+x^4/24.
--
-- These are exact Bishop-real inequalities obtained from concrete partial
-- sums, not imported Taylor axioms.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as NegExp
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Bracket
open import DASHI.Physics.YangMills.CompactLieProofLevel

half oneSixth oneTwentyFourth : BishopReal.ℝ
half = Exp.embed (+ 1 / 2)
oneSixth = Exp.embed (+ 1 / 6)
oneTwentyFourth = Exp.embed (+ 1 / 24)

square cube fourth : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x
cube x = BishopReal._*_ (square x) x
fourth x = BishopReal._*_ (square x) (square x)

lowerLinear : BishopReal.ℝ → BishopReal.ℝ
lowerLinear x = BishopReal._-_ BishopReal.1ℝ x

upperQuadratic : BishopReal.ℝ → BishopReal.ℝ
upperQuadratic x =
  BishopReal._+_
    (BishopReal._-_ BishopReal.1ℝ x)
    (BishopReal._*_ half (square x))

upperQuartic : BishopReal.ℝ → BishopReal.ℝ
upperQuartic x =
  BishopReal._+_
    (BishopReal._-_
      (BishopReal._+_
        (BishopReal._-_ BishopReal.1ℝ x)
        (BishopReal._*_ half (square x)))
      (BishopReal._*_ oneSixth (cube x)))
    (BishopReal._*_ oneTwentyFourth (fourth x))

magnitudeZero :
  ∀ {x} → NegExp.UnitIntervalPoint x →
  BishopReal._≃_ (Exp.expMagnitudeTerm x zero) BishopReal.1ℝ
magnitudeZero point =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ (+ 1 / 1) ⊗ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
    BishopP.≃-refl

magnitudeOne :
  ∀ {x} → NegExp.UnitIntervalPoint x →
  BishopReal._≃_ (Exp.expMagnitudeTerm x 1) x
magnitudeOne {x} point =
  BishopP.≃-trans
    (BishopP.*-congˡ (NegExp.powerAbsIsPower point 1))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x′ → Κ (+ 1 / 1) ⊗ (Κ 1ℚᵘ ⊗ x′) ⊜ x′)
        BishopP.≃-refl x)

magnitudeTwo :
  ∀ {x} → NegExp.UnitIntervalPoint x →
  BishopReal._≃_
    (Exp.expMagnitudeTerm x 2)
    (BishopReal._*_ half (square x))
magnitudeTwo {x} point =
  BishopP.≃-trans
    (BishopP.*-congˡ (NegExp.powerAbsIsPower point 2))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x′ → Κ (+ 1 / 2) ⊗ ((Κ 1ℚᵘ ⊗ x′) ⊗ x′)
          ⊜ Κ (+ 1 / 2) ⊗ (x′ ⊗ x′))
        BishopP.≃-refl x)

magnitudeThree :
  ∀ {x} → NegExp.UnitIntervalPoint x →
  BishopReal._≃_
    (Exp.expMagnitudeTerm x 3)
    (BishopReal._*_ oneSixth (cube x))
magnitudeThree {x} point =
  BishopP.≃-trans
    (BishopP.*-congˡ (NegExp.powerAbsIsPower point 3))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x′ → Κ (+ 1 / 6) ⊗ (((Κ 1ℚᵘ ⊗ x′) ⊗ x′) ⊗ x′)
          ⊜ Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′))
        BishopP.≃-refl x)

magnitudeFour :
  ∀ {x} → NegExp.UnitIntervalPoint x →
  BishopReal._≃_
    (Exp.expMagnitudeTerm x 4)
    (BishopReal._*_ oneTwentyFourth (fourth x))
magnitudeFour {x} point =
  BishopP.≃-trans
    (BishopP.*-congˡ (NegExp.powerAbsIsPower point 4))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x′ →
          Κ (+ 1 / 24) ⊗ ((((Κ 1ℚᵘ ⊗ x′) ⊗ x′) ⊗ x′) ⊗ x′)
          ⊜ Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′)))
        BishopP.≃-refl x)

lowerPartialOne :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≃_
    (Bracket.lowerPartial (NegExp.negativeExponentialInterlacing point) 1)
    (lowerLinear x)
lowerPartialOne {x} point =
  let
    dataSet = NegExp.negativeExponentialAlternatingData point
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-identityˡ BishopReal.0ℝ)
      (NegExp.oddTermIsNegativeMagnitude point zero))
    (let open BishopP.ℝ-Solver
     in solve 2
        (λ m0 m1 → (Κ 0ℚᵘ ⊕ m0) ⊕ (⊝ m1) ⊜ Κ 1ℚᵘ ⊖ x)
        BishopP.≃-refl
        (Exp.expMagnitudeTerm x zero)
        (Exp.expMagnitudeTerm x 1))

upperPartialOne :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≃_
    (Bracket.upperPartial (NegExp.negativeExponentialInterlacing point) 1)
    (upperQuadratic x)
upperPartialOne {x} point =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      (((Κ 0ℚᵘ ⊕ Κ (+ 1 / 1)) ⊕ (⊝ x′))
        ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
      ⊜ (Κ 1ℚᵘ ⊖ x′) ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
    BishopP.≃-refl x

upperPartialTwo :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≃_
    (Bracket.upperPartial (NegExp.negativeExponentialInterlacing point) 2)
    (upperQuartic x)
upperPartialTwo {x} point =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      (((((Κ 0ℚᵘ ⊕ Κ (+ 1 / 1)) ⊕ (⊝ x′))
          ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
          ⊕ (⊝ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′))))
          ⊕ (Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′))))
      ⊜ (((Κ 1ℚᵘ ⊖ x′) ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
          ⊖ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
          ⊕ (Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′))))
    BishopP.≃-refl x

negativeExpAboveLinear :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≤_ (lowerLinear x) (Exp.bishopExp (BishopReal.- x))
negativeExpAboveLinear point =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (lowerPartialOne point))
    (Bracket.lowerPartialBelowRepresentedLimit
      (NegExp.negativeExponentialInterlacing point) 1)

negativeExpBelowQuadratic :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≤_
    (Exp.bishopExp (BishopReal.- x))
    (upperQuadratic x)
negativeExpBelowQuadratic point =
  BishopP.≤-respʳ-≃
    (upperPartialOne point)
    (Bracket.representedLimitBelowUpperPartial
      (NegExp.negativeExponentialInterlacing point) 1)

negativeExpBelowQuartic :
  ∀ {x} (point : NegExp.UnitIntervalPoint x) →
  BishopReal._≤_
    (Exp.bishopExp (BishopReal.- x))
    (upperQuartic x)
negativeExpBelowQuartic point =
  BishopP.≤-respʳ-≃
    (upperPartialTwo point)
    (Bracket.representedLimitBelowUpperPartial
      (NegExp.negativeExponentialInterlacing point) 2)

bishopNegativeExponentialQuarticBracketLevel : ProofLevel
bishopNegativeExponentialQuarticBracketLevel = machineChecked
