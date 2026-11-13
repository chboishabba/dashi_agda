module DASHI.Moonshine.AbelBishopSelectedLogEightTwentySevenNormExact where

------------------------------------------------------------------------
-- SELECTED ACTUAL BISHOP LOCAL CHART: THE SHARP 8/27 REMAINDER.
--
-- Work on SAME original complex series, SAME selected p^-1*t chart:
--  N(p)>=(27/20)^2, N(t)<=(1/10)^2, u=p^-1*t.
-- The already constructed upper-disk theorem ensures |u|<=2/27.
--
-- Original Bishop finite-to-limit log estimate (proved separately):
--  ||R2(u)|| <= [ (1/2)*N(u) ] / [ 1-||u|| ].
--
-- NEW derived reciprocal estimates:
--  N(p)^-1 <= (20/27)^2 ;
--  (1-||u||)^-1 <= 27/25.
--
-- Therefore, without discarding true N(t):
--  ||R2(u)|| <= (1/2)*(20/27)^2*(27/25)*N(t)
--             = (8/27)*N(t).
--
-- This is the physical *selected Bishop p chart* numerical P1.L
-- inequality, NOT a standalone principal logarithm inverse or a
-- global Abel/Kneser continuation result.
--
-- All scalar inverses use genuine Bishop Inverse._⁻¹ and the
-- BishopPositiveInverseUpperFromLowerExact cross-multiplication
-- lemma. No order/theorem fields or synthetic chart values.
--
-- Remaining authority: existing R4.BishopSquareRootCalculus still
-- uninhabited on the original pinned Bishop-real carrier; source
-- pending exact-head native Agda 2.9 kernel acceptance.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Foundations.BishopSquareNonnegativeExact as Squares
import DASHI.Foundations.BishopPositiveInverseUpperFromLowerExact as InverseOrder
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as StepV
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopSelectedLocalLogDiskAdmissionExact as Selected
import DASHI.Moonshine.AbelBishopSelectedLogUpperDiskQuadraticTailExact as Tail
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormFiniteMajorantExact as Majorant
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormGeometricBoundExact as Geometric
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormLimitOrderExact as Limit
import DASHI.Moonshine.AbelBishopSelectedLogTrueNormRemainderExact as Chart

pInverseUpper : BishopReal.ℝ
pInverseUpper = Norm.square (BishopReal._⋆ (+ 20 / 27))

pInverseUpperNN : BishopReal.NonNegative pInverseUpper
pInverseUpperNN =
  Squares.bishopSquareNonnegative (BishopReal._⋆ (+ 20 / 27))

pLowerTimesInverseUpperIsOne :
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square Selected.selectedLowerModulus)
      pInverseUpper)
    BishopReal.1ℝ
pLowerTimesInverseUpperIsOne =
  let open BishopP.ℝ-Solver in
  solve 0
    ((((Κ (+ 27 / 20)) ⊗ (Κ (+ 27 / 20))) ⊗
      ((Κ (+ 20 / 27)) ⊗ (Κ (+ 20 / 27))))
     ⊜ (Κ 1ℚᵘ))
    BishopP.≃-refl

-- No arbitrary comparison: use the original SAME p norm lower.
originalSelectedPInverseNormSqUpper :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) →
  BishopReal._≤_
    (Norm.square Selected.selectedLowerModulus)
    (Norm.normSqC p) →
  BishopReal._≤_
    (BishopInverse._⁻¹ (Norm.normSqC p)
      (Reciprocal.normSquareNonzero nz))
    pInverseUpper
originalSelectedPInverseNormSqUpper p nz pLower =
  InverseOrder.positiveInverseBelowSupersolution
    (Norm.normSqC p)
    (Norm.square Selected.selectedLowerModulus)
    pInverseUpper
    (Reciprocal.normSquareNonzero nz)
    (Reciprocal.normSquarePositive nz)
    pLower pInverseUpperNN pLowerTimesInverseUpperIsOne

-- Exact original u=p^-1*t, not a free complex variable. Its true
-- norm square is <= (20/27)^2 * N(t).
originalSelectedRelativeNormSqBelowDisplacement :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  BishopReal._≤_
    (Norm.square Selected.selectedLowerModulus)
    (Norm.normSqC p) →
  BishopReal._≤_
    (Norm.normSqC (Affine.normalizedDisplacement p nz t))
    (BishopReal._*_ pInverseUpper (Norm.normSqC t))
originalSelectedRelativeNormSqBelowDisplacement p nz t pLower =
  BishopP.≤-respˡ-≃
    (Affine.originalBishopNormalizedDisplacementNormSquare p nz t)
    (BishopP.*-monoʳ-≤-nonNeg
      (originalSelectedPInverseNormSqUpper p nz pLower)
      (Upper.normSquareNonnegative t))

gapLower : BishopReal.ℝ
gapLower = BishopReal._⋆ (+ 25 / 27)

gapInverseUpper : BishopReal.ℝ
gapInverseUpper = BishopReal._⋆ (+ 27 / 25)

gapInverseUpperNN : BishopReal.NonNegative gapInverseUpper
gapInverseUpperNN =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopP.p<q⇒p⋆<q⋆
        0ℚᵘ (+ 27 / 25)
        (Data.Rational.Unnormalised.Properties.positive⁻¹ (+ 27 / 25))))

gapLowerTimesInverseUpperIsOne :
  BishopReal._≃_ (BishopReal._*_ gapLower gapInverseUpper)
    BishopReal.1ℝ
gapLowerTimesInverseUpperIsOne =
  let open BishopP.ℝ-Solver in
  solve 0
    ((Κ (+ 25 / 27) ⊗ Κ (+ 27 / 25)) ⊜ Κ 1ℚᵘ)
    BishopP.≃-refl

-- The source selected r is bounded by 2/27. The ordered Bishop
-- subtraction law yields 25/27 <= 1-r. No inverse bound is assumed.
originalSelectedGapLower :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w} →
  BishopReal._≤_
    (Majorant.trueBishopRadius roots w)
    Selected.selectedLogRelativeRadius →
  BishopReal._≤_
    gapLower
    (BishopReal._-_ BishopReal.1ℝ
      (Majorant.trueBishopRadius roots w))
originalSelectedGapLower roots {w} rBelow =
  let
    radius = Majorant.trueBishopRadius roots w
    maxRadius = Selected.selectedLogRelativeRadius
    maxGap = BishopReal._-_ BishopReal.1ℝ maxRadius

    differenceNN =
      BishopSequence.x≤y⇒0≤y-x rBelow

    shifted =
      BishopP.+-monoʳ-≤ maxGap differenceNN

    gapOrder =
      BishopP.≤-respʳ-≃
        (let open BishopP.ℝ-Solver in
         solve 2
           (λ rmax r →
             ((Κ 1ℚᵘ ⊖ rmax) ⊕ (rmax ⊖ r))
             ⊜ (Κ 1ℚᵘ ⊖ r))
           BishopP.≃-refl maxRadius radius)
        (BishopP.≤-respˡ-≃
          (BishopP.+-identityʳ maxGap) shifted)

    lowerIsMaxGap :
      BishopReal._≃_ gapLower maxGap
    lowerIsMaxGap =
      let open BishopP.ℝ-Solver in
      solve 0
        (Κ (+ 25 / 27) ⊜ (Κ 1ℚᵘ ⊖ Κ (+ 2 / 27)))
        BishopP.≃-refl
  in
  BishopP.≤-respˡ-≃ lowerIsMaxGap gapOrder

originalSelectedGapInverseUpper :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w} →
  BishopReal._≤_
    (Majorant.trueBishopRadius roots w)
    Selected.selectedLogRelativeRadius →
  (inside :
    BishopReal._<_
      (Majorant.trueBishopRadius roots w) BishopReal.1ℝ) →
  BishopReal._≤_
    (StepV.bishopGeometricUniformBound
      (Geometric.originalBishopTrueNormGeometricInputs
        roots w inside))
    gapInverseUpper
originalSelectedGapInverseUpper roots {w} rBelow inside =
  let
    inputs = Geometric.originalBishopTrueNormGeometricInputs
      roots w inside
  in
  InverseOrder.positiveInverseBelowSupersolution
    (StepV.oneMinusRatio inputs)
    gapLower gapInverseUpper
    (StepV.oneMinusRatioNonzero inputs)
    (StepV.oneMinusRatioPositive inputs)
    (originalSelectedGapLower roots rBelow)
    gapInverseUpperNN
    gapLowerTimesInverseUpperIsOne

eightOverTwentySeven : BishopReal.ℝ
eightOverTwentySeven = BishopReal._⋆ (+ 8 / 27)

-- Native Bishop ring arithmetic, with the literal selected
-- 27/20, 20/27, 27/25 factors; never floating-point rounding.
sharpCoefficientIsEightOverTwentySeven :
  ∀ n →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_
        (BishopReal._*_ Half.bishopHalf
          (BishopReal._*_ pInverseUpper n))
        gapInverseUpper)
      BishopReal.1ℝ)
    (BishopReal._*_ eightOverTwentySeven n)
sharpCoefficientIsEightOverTwentySeven n =
  let open BishopP.ℝ-Solver in
  solve 1
    (λ n →
      (((Κ (+ 1 / 2)) ⊗
          (((Κ (+ 20 / 27)) ⊗ (Κ (+ 20 / 27))) ⊗ n))
        ⊗ Κ (+ 27 / 25)) ⊗ Κ 1ℚᵘ
      ⊜ (Κ (+ 8 / 27) ⊗ n))
    BishopP.≃-refl n

-- Sharp SOURCE normalizer comparison, on the exact selected p chart.
originalSelectedSharpValueBelowEightOverTwentySeven :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  (pLower :
    BishopReal._≤_
      (Norm.square Selected.selectedLowerModulus)
      (Norm.normSqC p)) →
  (tInside :
    BishopReal._≤_
      (Norm.normSqC t)
      (Norm.square Selected.selectedLogRadius)) →
  let
    w = Affine.normalizedDisplacement p nz t
    disk = Tail.selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside
    inside = Limit.originalBishopTrueNormBelowOneFromDisk
      roots Selected.selectedLogRelativeInterval disk
  in BishopReal._≤_
    (Limit.originalBishopSharpQuadraticValue roots w inside)
    (BishopReal._*_ eightOverTwentySeven (Norm.normSqC t))
originalSelectedSharpValueBelowEightOverTwentySeven
    roots p nz t pLower tInside =
  let
    w = Affine.normalizedDisplacement p nz t
    disk = Tail.selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside
    inside = Limit.originalBishopTrueNormBelowOneFromDisk
      roots Selected.selectedLogRelativeInterval disk
    r = Majorant.trueBishopRadius roots w
    inputs = Geometric.originalBishopTrueNormGeometricInputs
      roots w inside
    invGap = StepV.bishopGeometricUniformBound inputs
    nt = Norm.normSqC t
    term = BishopReal._*_ Half.bishopHalf (Norm.square r)
    ntUpper = BishopReal._*_ pInverseUpper nt
    termUpper = BishopReal._*_ Half.bishopHalf ntUpper

    normSquareBound =
      BishopP.≤-respˡ-≃
        (R4.rootSquare roots (Norm.normSqC w)
          (Upper.normSquareNonnegative w))
        (originalSelectedRelativeNormSqBelowDisplacement
          p nz t pLower)

    termBound =
      BishopP.*-monoˡ-≤-nonNeg
        normSquareBound Half.bishopHalfNonnegative

    invGapNN =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (StepV.bishopGeometricUniformBoundPositive inputs))

    upperFirst =
      BishopP.*-monoʳ-≤-nonNeg termBound invGapNN

    upperTermNN =
      BishopP.nonNegx,y⇒nonNegx*y
        Half.bishopHalfNonnegative
        (BishopP.nonNegx,y⇒nonNegx*y
          pInverseUpperNN
          (Upper.normSquareNonnegative t))

    rBelow = Limit.originalBishopTrueNormBelowUpperDiskRadius
      roots disk

    gapBound = originalSelectedGapInverseUpper roots rBelow inside

    upperSecond =
      BishopP.*-monoˡ-≤-nonNeg gapBound upperTermNN

    finalAlgebra =
      BishopP.≃-trans
        (sharpCoefficientIsEightOverTwentySeven nt)
        (BishopP.*-identityʳ
          (BishopReal._*_ eightOverTwentySeven nt))
  in
  BishopP.≤-respʳ-≃
    finalAlgebra
    (BishopP.≤-trans upperFirst upperSecond)

-- THE ACTUAL ORIGINAL SELECTED BISHOP LOG SERIES:
--   ||R2(p^-1*t)|| <= (8/27)*N(t).
-- No fixed-point p is invented; the theorem holds for any original
-- p with its actual stated norm lower and apartness witness.
originalSelectedLogQuadraticEightOverTwentySeven :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  (pLower :
    BishopReal._≤_
      (Norm.square Selected.selectedLowerModulus)
      (Norm.normSqC p)) →
  (tInside :
    BishopReal._≤_
      (Norm.normSqC t)
      (Norm.square Selected.selectedLogRadius)) →
  BishopReal._≤_
    (Majorant.trueBishopRadius roots
      (Tail.selectedOriginalLogQuadraticTailLimit
        p nz t pLower tInside))
    (BishopReal._*_ eightOverTwentySeven (Norm.normSqC t))
originalSelectedLogQuadraticEightOverTwentySeven
    roots p nz t pLower tInside =
  BishopP.≤-trans
    (Chart.originalSelectedTrueNormRemainder
      roots p nz t pLower tInside)
    (originalSelectedSharpValueBelowEightOverTwentySeven
      roots p nz t pLower tInside)
