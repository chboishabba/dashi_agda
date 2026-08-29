module DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact where

------------------------------------------------------------------------
-- exp(-x) IS A CONSTRUCTIVE UNIT-INTERVAL RATIO FOR 0 < x <= 1
------------------------------------------------------------------------

open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as NegExp
import DASHI.Foundations.BishopNegativeExponentialQuarticBracketExact as Bracket
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PositiveUnitIntervalPoint (x : BishopReal.ℝ) : Set₁ where
  field
    unitPoint : NegExp.UnitIntervalPoint x
    positive : BishopReal._<_ BishopReal.0ℝ x

open PositiveUnitIntervalPoint public

xSquareBelowX :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._≤_ (Bracket.square x) x
xSquareBelowX {x} inputs =
  let
    point = unitPoint inputs
    raw =
      BishopP.*-monoˡ-≤-nonNeg
        (NegExp.belowOne point)
        (NegExp.nonnegative point)
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityʳ x)
    raw

halfNonnegative : BishopReal.NonNegative Bracket.half
halfNonnegative =
  BishopP.0≤x⇒nonNegx (BishopP.<⇒≤ Exp.halfPositive)

halfTimesXBelowX :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._<_
    (BishopReal._*_ Bracket.half x)
    x
halfTimesXBelowX {x} inputs =
  BishopP.<-respʳ-≃
    (BishopP.*-identityˡ x)
    (BishopP.*-monoˡ-<-pos
      (BishopP.0<x⇒posx (positive inputs))
      Exp.halfBelowOne)

halfSquareBelowX :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._<_
    (BishopReal._*_ Bracket.half (Bracket.square x))
    x
halfSquareBelowX inputs =
  BishopP.≤-<-trans
    (BishopP.*-monoˡ-≤-nonNeg
      (xSquareBelowX inputs)
      halfNonnegative)
    (halfTimesXBelowX inputs)

upperQuadraticBelowOne :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._<_ (Bracket.upperQuadratic x) BishopReal.1ℝ
upperQuadraticBelowOne {x} inputs =
  let
    shifted =
      BishopP.+-monoʳ-<
        (BishopReal._-_ BishopReal.1ℝ x)
        (halfSquareBelowX inputs)
    cancellation :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._-_ BishopReal.1ℝ x)
          x)
        BishopReal.1ℝ
    cancellation =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ x′ → (Κ 1ℚᵘ ⊖ x′) ⊕ x′ ⊜ Κ 1ℚᵘ)
        BishopP.≃-refl x
  in
  BishopP.<-respʳ-≃ cancellation shifted

negativeExpNonnegative :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._≤_
    BishopReal.0ℝ
    (Exp.bishopExp (BishopReal.- x))
negativeExpNonnegative {x} inputs =
  let
    point = unitPoint inputs
    lowerNonnegative =
      BishopSequence.x≤y⇒0≤y-x (NegExp.belowOne point)
  in
  BishopP.≤-trans
    lowerNonnegative
    (Bracket.negativeExpAboveLinear point)

negativeExpBelowOne :
  ∀ {x} → PositiveUnitIntervalPoint x →
  BishopReal._<_
    (Exp.bishopExp (BishopReal.- x))
    BishopReal.1ℝ
negativeExpBelowOne inputs =
  BishopP.≤-<-trans
    (Bracket.negativeExpBelowQuadratic (unitPoint inputs))
    (upperQuadraticBelowOne inputs)

negativeExpUnitRatio :
  ∀ {x} → PositiveUnitIntervalPoint x →
  Geometric.BishopUnitIntervalRatio
    (Exp.bishopExp (BishopReal.- x))
negativeExpUnitRatio inputs = record
  { ratioNonnegative = negativeExpNonnegative inputs
  ; ratioBelowOne = negativeExpBelowOne inputs
  }

bishopNegativeExponentialUnitIntervalLevel : ProofLevel
bishopNegativeExponentialUnitIntervalLevel = machineChecked
