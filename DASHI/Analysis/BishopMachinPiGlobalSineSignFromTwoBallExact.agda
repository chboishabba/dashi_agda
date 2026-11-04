{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinPiGlobalSineSignFromTwoBallExact where

------------------------------------------------------------------------
-- K05-PI: THE FULL ORIGINAL BISHOP MACHIN FIRST-ZERO SIGN CUT.
--
-- Existing source facts:
--  * pi_M < 22/7 and the original Machin arctangent quarter branch;
--  * strict sin_B(t)>0 for 0<t and |t|<=2, proved independently
--    from the original signed-factorial radius-two cubic estimate;
--  * pi_M-complement reflection of the selected Round11 sine,
--    derived from the SAME already-owed K05 imaginary product and
--    quarter-angle cosine/sine identity;
--  * the pinned Bishop REAL locatedness theorem
--    fast-corollary-2-17: for 3/2<2, every x has x<2 OR 3/2<x.
--
-- For 0<x<pi_M:
--   if x<2, positivity follows from the radius-two theorem;
--   if 3/2<x, pi_M-x < 22/7-3/2 = 23/14 < 2,
--     and sin_B(x) = sin_B(pi_M-x) > 0 by native reflection.
--
-- Thus no separate globally assumed sign theorem, classical
-- trichotomy, derivative, angle monotonicity, or symbolic pi is
-- required. The COMPLETE first-positive sine zero is compiled
-- from just the original K05 imaginary product + original
-- arctangent/tangent quarter identity, BOTH still independent
-- analytic theorem gates.
--
-- Bishop/Bridges, Murray/Csimma, Machin; original DASHI
-- Balaban sine cubic and Riemann locatedness theorem owners.
-- Source-written, Agda kernel receipt pending.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Unnormalised as Q using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Analysis.BishopSinePositiveTwoBallFromCubicExact as SinePos
import DASHI.Analysis.BishopMachinPiComplementReflectionFromImaginaryProductExact as Reflection
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as TwoBall
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

middle : R.ℝ
middle = R._⋆ (+ 3 / 2)

upper : R.ℝ
upper = Window.embed Window.twentyTwoSevenths

differenceUpper : R.ℝ
differenceUpper = R._⋆ (+ 23 / 14)

middleBelowTwo : R._<_ middle TwoBall.bishopTwo
middleBelowTwo =
  RP.p<q⇒p⋆<q⋆
    (+ 3 / 2) TwoBall.two
    (toWitness {a? = QP._<?_ (+ 3 / 2) TwoBall.two} _)

differenceUpperBelowTwo : R._<_ differenceUpper TwoBall.bishopTwo
differenceUpperBelowTwo =
  RP.p<q⇒p⋆<q⋆
    (+ 23 / 14) TwoBall.two
    (toWitness {a? = QP._<?_ (+ 23 / 14) TwoBall.two} _)

upperMinusMiddleIsDifferenceUpper :
  R._≃_
    (R._+_ upper (R.-_ middle))
    differenceUpper
upperMinusMiddleIsDifferenceUpper =
  let open RP.ℝ-Solver
  in solve 0
    ((Κ (+ 22 / 7)) ⊕ (⊝ (Κ (+ 3 / 2))))
      ⊜ (Κ (+ 23 / 14))
    RP.≃-refl

machinComplementBelowTwoFromLocatedRight :
  (x : R.ℝ) →
  R._<_ middle x →
  R._<_ (Reflection.machinComplement x) TwoBall.bishopTwo
machinComplementBelowTwoFromLocatedRight x middleBelowX =
  let
    negativeXBelowNegativeMiddle :
      R._<_ (R.-_ x) (R.-_ middle)
    negativeXBelowNegativeMiddle =
      RP.neg-mono-< middleBelowX

    firstBound :
      R._<_
        (R._+_ (R.-_ x) Machin.bishopMachinPi)
        (R._+_ upper (R.-_ x))
    firstBound =
      RP.<-respʳ-≃
        (RP.+-comm (R.-_ x) upper)
        (RP.+-monoʳ-< (R.-_ x)
          Window.machinPiBelowTwentyTwoSevenths)

    secondBound :
      R._<_
        (R._+_ upper (R.-_ x))
        differenceUpper
    secondBound =
      RP.<-respʳ-≃ upperMinusMiddleIsDifferenceUpper
        (RP.+-monoʳ-< upper negativeXBelowNegativeMiddle)

    combined :
      R._<_
        (R._+_ (R.-_ x) Machin.bishopMachinPi)
        TwoBall.bishopTwo
    combined =
      RP.<-trans
        (RP.<-trans firstBound secondBound)
        differenceUpperBelowTwo
  in
  RP.<-respˡ-≃
    (RP.≃-symm (Reflection.machinComplementAsNegativePlusPi x))
    combined

machinComplementInsideTwoFromLocatedRight :
  (x : R.ℝ) →
  R._<_ x Machin.bishopMachinPi →
  R._<_ middle x →
  R._≤_
    (R.∣_∣ (Reflection.machinComplement x))
    TwoBall.bishopTwo
machinComplementInsideTwoFromLocatedRight x xBelowPi middleBelowX =
  let
    compPositive :
      R._<_ R.0ℝ (Reflection.machinComplement x)
    compPositive =
      RP.x<y⇒0<y-x x Machin.bishopMachinPi xBelowPi

    compNN : R.NonNegative (Reflection.machinComplement x)
    compNN = RP.0≤x⇒nonNegx (RP.<⇒≤ compPositive)
  in
  RP.≤-respˡ-≃
    (RP.≃-symm (RP.nonNegx⇒∣x∣≃x compNN))
    (RP.<⇒≤
      (machinComplementBelowTwoFromLocatedRight x middleBelowX))

round11SinePositiveBeforeMachinPi :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  First.NativeSinePositiveBeforeMachinPi inputs
round11SinePositiveBeforeMachinPi inputs product quarterEqual
    x xPositive xBelowPi
  with RP.fast-corollary-2-17
    x middle TwoBall.bishopTwo middleBelowTwo
... | inj₁ xBelowTwo =
  SinePos.round11SinePositiveOnStrictTwoBall
    inputs x xPositive
    (RP.≤-respˡ-≃
      (RP.≃-symm (RP.nonNegx⇒∣x∣≃x
        (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))))
      (RP.<⇒≤ xBelowTwo))
... | inj₂ middleBelowX =
  RP.<-respʳ-≃
    (Reflection.round11SineMachinComplement
      inputs product quarterEqual x)
    (SinePos.round11SinePositiveOnStrictTwoBall
      inputs
      (Reflection.machinComplement x)
      (RP.x<y⇒0<y-x x Machin.bishopMachinPi xBelowPi)
      (machinComplementInsideTwoFromLocatedRight
        x xBelowPi middleBelowX))

-- No formerly free global-sign input remains: source-owned
-- locatedness + cubic sine positivity + SAME product/quarter inputs.
round11MachinPiIsFirstPositiveSineZero :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  First.SourceMachinFirstPositiveSineZero inputs
round11MachinPiIsFirstPositiveSineZero inputs product quarterEqual =
  First.sourceMachinFirstSineZeroFromNativePhase
    inputs product quarterEqual
    (round11SinePositiveBeforeMachinPi inputs product quarterEqual)
