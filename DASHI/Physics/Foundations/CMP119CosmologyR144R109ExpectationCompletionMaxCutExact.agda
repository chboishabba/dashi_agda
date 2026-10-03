{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact where

------------------------------------------------------------------------
-- R144 FINITE ONE-POINT EXPECTATION -> R109/R136 COMPLETION MAX-CUT.
--
-- The finite operator/sign orientation is already fixed elsewhere:
--
--   D_h Gamma_k = <T_h>_k
--
-- for the same selected R144/R119 stress insertion.  R109 already supplies a
-- summable Cauchy modulus for that selected stress coordinate.  The remaining
-- absolute-value issue is only to anchor the finite normalized expectation to
-- the completed response.
--
-- This file packages the sharp quantitative form actually needed for the
-- universe-expansion sign:
--
--   completed <= finite_k + remainingTail_k.
--
-- Therefore if
--
--   finite_k + remainingTail_k < 0,
--
-- the completed R136 expectation is strictly negative.  No generic theorem
-- saying "limits preserve strict signs" is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

r109RemainingTail :
  R109.SourceNativeStressScaleCauchy → Nat → ℚ
r109RemainingTail source start =
  Scale.coefficient
    (Sum.commonMajorant
      (Source.sourceCompatibleSameFamilyIncrement
        (R109.source source)
        (R109.smallHistory source)
        (R109.stressInsertion source)))
  * (Geo.half * Geo.halfPower start)

record R144R109AbsoluteExpectationCompletion
    (source : R109.SourceNativeStressScaleCauchy) : Set₁ where
  field
    finiteExpectation : Nat → ℚ
    completedExpectation : ℚ

    -- The one remaining absolute anchoring theorem.  It should be obtained by
    -- identifying finiteExpectation with the R144 D_Gamma expectation and the
    -- completed value with the selected R109/R136 stress readout.
    completionUpperTail : ∀ start →
      completedExpectation
      ≤ finiteExpectation start + r109RemainingTail source start

open R144R109AbsoluteExpectationCompletion public

negativeFiniteMarginForcesNegativeCompletion :
  ∀ {source : R109.SourceNativeStressScaleCauchy}
    (anchor : R144R109AbsoluteExpectationCompletion source)
    start →
  finiteExpectation anchor start + r109RemainingTail source start < 0ℚ →
  completedExpectation anchor < 0ℚ
negativeFiniteMarginForcesNegativeCompletion anchor start marginNegative =
  ℚP.≤-<-trans
    (completionUpperTail anchor start)
    marginNegative

negativeFiniteResponseWithExplicitTailMargin :
  ∀ {source : R109.SourceNativeStressScaleCauchy}
    (anchor : R144R109AbsoluteExpectationCompletion source)
    start margin →
  finiteExpectation anchor start ≤ - margin →
  r109RemainingTail source start < margin →
  completedExpectation anchor < 0ℚ
negativeFiniteResponseWithExplicitTailMargin
    {source = source} anchor start margin finiteBelow tailBelow =
  let
    summed :
      finiteExpectation anchor start + r109RemainingTail source start
      < (- margin) + margin
    summed =
      ℚP.+-mono-≤-< finiteBelow tailBelow

    summedBelowZero :
      finiteExpectation anchor start + r109RemainingTail source start < 0ℚ
    summedBelowZero =
      subst
        (λ right →
          finiteExpectation anchor start + r109RemainingTail source start < right)
        (Ring.solve-∀ margin)
        summed
  in
  negativeFiniteMarginForcesNegativeCompletion
    anchor start summedBelowZero

r109CauchyEstimateAlreadyOwned : Bool
r109CauchyEstimateAlreadyOwned = true

finiteOperatorOrientationAlreadyOwned : Bool
finiteOperatorOrientationAlreadyOwned = true

remainingBResidualIsAbsoluteExpectationAnchor : Bool
remainingBResidualIsAbsoluteExpectationAnchor = true
