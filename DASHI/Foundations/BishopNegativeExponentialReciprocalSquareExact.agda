module DASHI.Foundations.BishopNegativeExponentialReciprocalSquareExact where

------------------------------------------------------------------------
-- SHARP SCALAR INEQUALITY FOR THE ERDOS DEGREE-ONE KERNEL
--
-- For 0 < x <= 1, q = exp(-x) satisfies
--
--     q x^2 < (1-q)^2.
--
-- The proof uses only the concrete quartic alternating upper bracket and the
-- polynomial factorization
--
-- (1-U4)^2 - U4*x^2
--   = x^4/576 * [9 + (1-x)(39-9x+7x^2-x^3)].
--
-- The second factor is nonnegative because
--
-- 39-9x+7x^2-x^3
--   = 29 + 9(1-x) + (1-x^3) + 7x^2.
--
-- No differentiation, logarithm, exp-additivity or classical root argument is
-- used.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as NegExp
import DASHI.Foundations.BishopNegativeExponentialQuarticBracketExact as Bracket
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alt
open import DASHI.Physics.YangMills.CompactLieProofLevel

q : BishopReal.ℝ → BishopReal.ℝ
q x = Exp.bishopExp (BishopReal.- x)

gap : BishopReal.ℝ → BishopReal.ℝ
gap value = BishopReal._-_ BishopReal.1ℝ value

nine twentyNine seven oneFiveSeventySixth : BishopReal.ℝ
nine = Exp.embed (+ 9 / 1)
twentyNine = Exp.embed (+ 29 / 1)
seven = Exp.embed (+ 7 / 1)
oneFiveSeventySixth = Exp.embed (+ 1 / 576)

cubeBelowOne :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._≤_ (Bracket.cube x) BishopReal.1ℝ
cubeBelowOne {x} inputs =
  let
    point = Unit.unitPoint inputs
    raw =
      BishopSequence.x≤y∧nonNegx⇒xⁿ≤yⁿ
        3 (NegExp.belowOne point) (NegExp.nonnegative point)
    leftPower :
      BishopReal._≃_ (BishopReal.pow x 3) (Bracket.cube x)
    leftPower =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ x′ → (((Κ 1ℚᵘ ⊗ x′) ⊗ x′) ⊗ x′)
          ⊜ (x′ ⊗ x′) ⊗ x′)
        BishopP.≃-refl x
    rightPower :
      BishopReal._≃_
        (BishopReal.pow BishopReal.1ℝ 3)
        BishopReal.1ℝ
    rightPower =
      let open BishopP.ℝ-Solver
      in solve 0
        ((((Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊗ Κ 1ℚᵘ) ⊗ Κ 1ℚᵘ)
          ⊜ Κ 1ℚᵘ)
        BishopP.≃-refl
  in
  BishopP.≤-respʳ-≃ rightPower
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm leftPower) raw)

oneMinusXNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (gap x)
oneMinusXNonnegative inputs =
  BishopP.0≤x⇒nonNegx
    (BishopSequence.x≤y⇒0≤y-x
      (NegExp.belowOne (Unit.unitPoint inputs)))

oneMinusCubeNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (gap (Bracket.cube x))
oneMinusCubeNonnegative inputs =
  BishopP.0≤x⇒nonNegx
    (BishopSequence.x≤y⇒0≤y-x (cubeBelowOne inputs))

squareNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (Bracket.square x)
squareNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx*y
    (NegExp.nonnegative (Unit.unitPoint inputs))
    (NegExp.nonnegative (Unit.unitPoint inputs))

scaledNonnegative :
  (scale value : BishopReal.ℝ) →
  BishopReal.NonNegative scale →
  BishopReal.NonNegative value →
  BishopReal.NonNegative (BishopReal._*_ scale value)
scaledNonnegative scale value = BishopP.nonNegx,y⇒nonNegx*y

nineNonnegative twentyNineNonnegative sevenNonnegative : BishopReal.NonNegative _
nineNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 9 / 1) (ℚP.nonNegative⁻¹ (+ 9 / 1)))
twentyNineNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 29 / 1) (ℚP.nonNegative⁻¹ (+ 29 / 1)))
sevenNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 7 / 1) (ℚP.nonNegative⁻¹ (+ 7 / 1)))

nineTimesOneMinusXNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (BishopReal._*_ nine (gap x))
nineTimesOneMinusXNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx*y nineNonnegative (oneMinusXNonnegative inputs)

sevenSquareNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (BishopReal._*_ seven (Bracket.square x))
sevenSquareNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx*y sevenNonnegative (squareNonnegative inputs)

remainderCore : BishopReal.ℝ → BishopReal.ℝ
remainderCore x =
  BishopReal._+_
    (BishopReal._+_
      (BishopReal._+_
        twentyNine
        (BishopReal._*_ nine (gap x)))
      (gap (Bracket.cube x)))
    (BishopReal._*_ seven (Bracket.square x))

remainderCoreNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (remainderCore x)
remainderCoreNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx+y
    (BishopP.nonNegx,y⇒nonNegx+y
      (BishopP.nonNegx,y⇒nonNegx+y
        twentyNineNonnegative
        (nineTimesOneMinusXNonnegative inputs))
      (oneMinusCubeNonnegative inputs))
    (sevenSquareNonnegative inputs)

cubicFactor : BishopReal.ℝ → BishopReal.ℝ
cubicFactor x =
  let open BishopP.ℝ-Solver
  in
  BishopReal._+_
    (BishopReal._-_
      (BishopReal._+_ (Exp.embed (+ 39 / 1))
        (BishopReal._*_ seven (Bracket.square x)))
      (BishopReal._*_ nine x))
    (BishopReal.- (Bracket.cube x))

cubicFactorIsRemainderCore : ∀ x →
  BishopReal._≃_ (cubicFactor x) (remainderCore x)
cubicFactorIsRemainderCore x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      ((Κ (+ 39 / 1) ⊕ (Κ (+ 7 / 1) ⊗ (x′ ⊗ x′)))
        ⊖ (Κ (+ 9 / 1) ⊗ x′)) ⊖ ((x′ ⊗ x′) ⊗ x′)
      ⊜ ((Κ (+ 29 / 1) ⊕ (Κ (+ 9 / 1) ⊗ (Κ 1ℚᵘ ⊖ x′)))
          ⊕ (Κ 1ℚᵘ ⊖ ((x′ ⊗ x′) ⊗ x′)))
          ⊕ (Κ (+ 7 / 1) ⊗ (x′ ⊗ x′)))
    BishopP.≃-refl x

cubicFactorNonnegative :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.NonNegative (cubicFactor x)
cubicFactorNonnegative inputs =
  BishopP.nonNeg-cong
    (BishopP.≃-symm (cubicFactorIsRemainderCore _))
    (remainderCoreNonnegative inputs)

polynomialFactor : BishopReal.ℝ → BishopReal.ℝ
polynomialFactor x =
  BishopReal._+_
    nine
    (BishopReal._*_ (gap x) (cubicFactor x))

ninePositive : BishopReal._<_ BishopReal.0ℝ nine
ninePositive =
  BishopP.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 9 / 1) (ℚP.positive⁻¹ (+ 9 / 1))

polynomialFactorPositive :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._<_ BishopReal.0ℝ (polynomialFactor x)
polynomialFactorPositive inputs =
  let
    productNN =
      BishopP.nonNegx,y⇒nonNegx*y
        (oneMinusXNonnegative inputs)
        (cubicFactorNonnegative inputs)
    nine≤factor =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ nine))
        (BishopP.+-monoʳ-≤ nine (BishopP.nonNegx⇒0≤x productNN))
  in
  BishopP.<-≤-trans ninePositive nine≤factor

fourthPositive :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal.Positive (Bracket.fourth x)
fourthPositive inputs =
  let xPositive = BishopP.0<x⇒posx (Unit.positive inputs)
      squarePositive = BishopP.posx,y⇒posx*y xPositive xPositive
  in BishopP.posx,y⇒posx*y squarePositive squarePositive

oneFiveSeventySixthPositive : BishopReal.Positive oneFiveSeventySixth
oneFiveSeventySixthPositive =
  BishopP.posp⇒posp⋆ (+ 1 / 576) (ℚP.positive⁻¹ (+ 1 / 576))

factorization : ∀ x →
  BishopReal._≃_
    (BishopReal._-_
      (Bracket.square (gap (Bracket.upperQuartic x)))
      (BishopReal._*_ (Bracket.upperQuartic x) (Bracket.square x)))
    (BishopReal._*_
      oneFiveSeventySixth
      (BishopReal._*_
        (Bracket.fourth x)
        (polynomialFactor x)))
factorization x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      (((Κ 1ℚᵘ ⊖
          ((((Κ 1ℚᵘ ⊖ x′) ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
             ⊖ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊕ (Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′)))))
        ⊗ (Κ 1ℚᵘ ⊖
          ((((Κ 1ℚᵘ ⊖ x′) ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
             ⊖ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊕ (Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′)))))
       ⊖ (((((Κ 1ℚᵘ ⊖ x′) ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
             ⊖ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊕ (Κ (+ 1 / 24) ⊗ ((x′ ⊗ x′) ⊗ (x′ ⊗ x′))))
             ⊗ (x′ ⊗ x′)))
      ⊜ Κ (+ 1 / 576) ⊗
          (((x′ ⊗ x′) ⊗ (x′ ⊗ x′)) ⊗
            (Κ (+ 9 / 1) ⊕
              ((Κ 1ℚᵘ ⊖ x′) ⊗
                ((((Κ (+ 39 / 1) ⊕ (Κ (+ 7 / 1) ⊗ (x′ ⊗ x′)))
                   ⊖ (Κ (+ 9 / 1) ⊗ x′))
                   ⊖ ((x′ ⊗ x′) ⊗ x′)))))))
    BishopP.≃-refl x

quarticCrossDifferencePositive :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._-_
      (Bracket.square (gap (Bracket.upperQuartic x)))
      (BishopReal._*_ (Bracket.upperQuartic x) (Bracket.square x)))
quarticCrossDifferencePositive {x} inputs =
  let
    rightPositive =
      BishopP.posx⇒0<x
        (BishopP.posx,y⇒posx*y
          oneFiveSeventySixthPositive
          (BishopP.posx,y⇒posx*y
            (fourthPositive inputs)
            (BishopP.0<x⇒posx (polynomialFactorPositive inputs))))
  in
  BishopP.<-respʳ-≃
    (BishopP.≃-symm (factorization x))
    rightPositive

quarticCrossInequality :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._<_
    (BishopReal._*_ (Bracket.upperQuartic x) (Bracket.square x))
    (Bracket.square (gap (Bracket.upperQuartic x)))
quarticCrossInequality {x} inputs =
  BishopP.0<y-x⇒x<y
    (BishopReal._*_ (Bracket.upperQuartic x) (Bracket.square x))
    (Bracket.square (gap (Bracket.upperQuartic x)))
    (quarticCrossDifferencePositive inputs)

upperQuarticBelowQuadratic :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≤_ (Bracket.upperQuartic x) (Bracket.upperQuadratic x)
upperQuarticBelowQuadratic {x} inputs =
  let
    point = Unit.unitPoint inputs
    dataSet = NegExp.negativeExponentialAlternatingData point
    raw = Alt.upperPartialDecreasing dataSet 1
  in
  BishopP.≤-respʳ-≃
    (Bracket.upperPartialOne point)
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm (Bracket.upperPartialTwo point))
      raw)

upperQuarticBelowOne :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._<_ (Bracket.upperQuartic x) BishopReal.1ℝ
upperQuarticBelowOne inputs =
  BishopP.≤-<-trans
    (upperQuarticBelowQuadratic inputs)
    (Unit.upperQuadraticBelowOne inputs)

upperGapNonnegative :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal.NonNegative (gap (Bracket.upperQuartic x))
upperGapNonnegative inputs =
  BishopP.0≤x⇒nonNegx
    (BishopP.<⇒≤
      (BishopP.x<y⇒0<y-x
        _ _ (upperQuarticBelowOne inputs)))

qGapNonnegative :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal.NonNegative (gap (q x))
qGapNonnegative inputs =
  BishopP.0≤x⇒nonNegx
    (BishopP.<⇒≤
      (BishopP.x<y⇒0<y-x
        _ _ (Unit.negativeExpBelowOne inputs)))

qTimesSquareBelowUpperTimesSquare :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≤_
    (BishopReal._*_ (q x) (Bracket.square x))
    (BishopReal._*_ (Bracket.upperQuartic x) (Bracket.square x))
qTimesSquareBelowUpperTimesSquare inputs =
  BishopP.*-monoʳ-≤-nonNeg
    (Bracket.negativeExpBelowQuartic (Unit.unitPoint inputs))
    (squareNonnegative inputs)
  where
  squareNonnegative :
    ∀ {x} → Unit.PositiveUnitIntervalPoint x →
    BishopReal.NonNegative (Bracket.square x)
  squareNonnegative inputs′ =
    BishopP.nonNegx,y⇒nonNegx*y
      (NegExp.nonnegative (Unit.unitPoint inputs′))
      (NegExp.nonnegative (Unit.unitPoint inputs′))

upperGapBelowQGap :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≤_
    (gap (Bracket.upperQuartic x))
    (gap (q x))
upperGapBelowQGap inputs =
  BishopP.+-monoˡ-≤
    BishopReal.1ℝ
    (BishopP.neg-mono-≤
      (Bracket.negativeExpBelowQuartic (Unit.unitPoint inputs)))

upperGapSquareBelowQGapSquare :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._≤_
    (Bracket.square (gap (Bracket.upperQuartic x)))
    (Bracket.square (gap (q x)))
upperGapSquareBelowQGapSquare inputs =
  BishopP.*-mono-≤
    (upperGapNonnegative inputs)
    (upperGapNonnegative inputs)
    (upperGapBelowQGap inputs)
    (upperGapBelowQGap inputs)

negativeExpCrossReciprocalSquare :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._<_
    (BishopReal._*_ (q x) (Bracket.square x))
    (Bracket.square (gap (q x)))
negativeExpCrossReciprocalSquare inputs =
  BishopP.≤-<-trans
    (qTimesSquareBelowUpperTimesSquare inputs)
    (BishopP.<-≤-trans
      (quarticCrossInequality inputs)
      (upperGapSquareBelowQGapSquare inputs))

bishopNegativeExponentialReciprocalSquareCrossLevel : ProofLevel
bishopNegativeExponentialReciprocalSquareCrossLevel = machineChecked
