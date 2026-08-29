{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalHistoryGateExact where

------------------------------------------------------------------------
-- ROW A: O(gamma) HISTORY RESPONSE -> ONE CANONICAL SMALL-COUPLING GATE
--
-- The honest total shooting gate after separating marginal and irrelevant
-- response is
--
--   L gammaTube + b_* qHistory < b_*,       b_* = b - C gamma.
--
-- If the literal irrelevant-history sensitivity is itself small-coupling
-- suppressed,
--
--   qHistory <= H gamma,
--
-- and gammaTube <= gamma, then it is enough to require
--
--   (C + L + b H) gamma < b.
--
-- Indeed b_* <= b, so b_* qHistory <= b H gamma.  This file proves that
-- implication exactly.  Consequently, once source analysis produces finite
-- C,L,H and b>0, the history-augmented gate is again paid by a single
-- sufficiently-small coupling choice.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

scaleRightNonnegative : ∀ {left right scale : ℚ} →
  0ℚ ≤ scale → left ≤ right → left * scale ≤ right * scale
scaleRightNonnegative {scale = scale} scaleNN leftBelowRight =
  let
    instance
      scaleNonnegative : NonNegative scale
      scaleNonnegative = ℚ.nonNegative scaleNN
  in
  ℚP.*-monoʳ-≤-nonNeg scale leftBelowRight

record AugmentedHistorySmallCouplingGate : Set where
  field
    gaussianFloor interactionConstant localDerivative historySlope : ℚ
    couplingCap tubeWidth historyConstant : ℚ

    gaussianFloorPositive : 0ℚ < gaussianFloor
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    localDerivativeNonnegative : 0ℚ ≤ localDerivative
    historySlopeNonnegative : 0ℚ ≤ historySlope
    couplingCapNonnegative : 0ℚ ≤ couplingCap
    tubeWidthNonnegative : 0ℚ ≤ tubeWidth
    historyConstantNonnegative : 0ℚ ≤ historyConstant

    tubeWidthBelowCap : tubeWidth ≤ couplingCap
    historyBelowSlopeTimesCap :
      historyConstant ≤ historySlope * couplingCap

    combinedSmallness :
      (interactionConstant + localDerivative + gaussianFloor * historySlope)
        * couplingCap
      < gaussianFloor

open AugmentedHistorySmallCouplingGate public

betaMargin : AugmentedHistorySmallCouplingGate → ℚ
betaMargin dataSet =
  gaussianFloor dataSet
    - interactionConstant dataSet * couplingCap dataSet

interactionPartBelowCombined :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  interactionConstant dataSet * couplingCap dataSet
  ≤ (interactionConstant dataSet + localDerivative dataSet
      + gaussianFloor dataSet * historySlope dataSet)
      * couplingCap dataSet
interactionPartBelowCombined dataSet =
  let
    C = interactionConstant dataSet
    L = localDerivative dataSet
    b = gaussianFloor dataSet
    H = historySlope dataSet

    bNN : 0ℚ ≤ b
    bNN = ℚP.<⇒≤ (gaussianFloorPositive dataSet)

    bHNN : 0ℚ ≤ b * H
    bHNN =
      let instance bNonnegative = ℚ.nonNegative bNN
          hNonnegative = ℚ.nonNegative (historySlopeNonnegative dataSet)
      in ℚP.nonNegative⁻¹ (b * H)

    cBelowCL : C ≤ C + L
    cBelowCL =
      subst
        (λ left → left ≤ C + L)
        (ℚP.+-identityʳ C)
        (ℚP.+-monoʳ-≤ C (localDerivativeNonnegative dataSet))

    clBelow : C + L ≤ C + L + b * H
    clBelow =
      subst
        (λ left → left ≤ C + L + b * H)
        (ℚP.+-identityʳ (C + L))
        (ℚP.+-monoʳ-≤ (C + L) bHNN)

    cBelow : C ≤ C + L + b * H
    cBelow = ℚP.≤-trans cBelowCL clBelow
  in
  scaleRightNonnegative (couplingCapNonnegative dataSet) cBelow

betaMarginPositive :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  0ℚ < betaMargin dataSet
betaMarginPositive dataSet =
  let
    Cg = interactionConstant dataSet * couplingCap dataSet
    CgBelowCombined = interactionPartBelowCombined dataSet
    CgBelowB : Cg < gaussianFloor dataSet
    CgBelowB = ℚP.≤-<-trans CgBelowCombined (combinedSmallness dataSet)
    shifted = ℚP.+-monoʳ-< (- Cg) CgBelowB
  in
  subst
    (λ left → left < betaMargin dataSet)
    (ℚRing.solve-∀ Cg)
    (subst
      (λ right → Cg + (- Cg) < right)
      (ℚRing.solve-∀ (gaussianFloor dataSet) Cg)
      shifted)

betaMarginBelowGaussian :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  betaMargin dataSet ≤ gaussianFloor dataSet
betaMarginBelowGaussian dataSet =
  let
    b = gaussianFloor dataSet
    Cg = interactionConstant dataSet * couplingCap dataSet

    CgNN : 0ℚ ≤ Cg
    CgNN =
      let instance cNN = ℚ.nonNegative (interactionConstantNonnegative dataSet)
          gNN = ℚ.nonNegative (couplingCapNonnegative dataSet)
      in ℚP.nonNegative⁻¹ Cg

    negBelowZeroRaw : 0ℚ + (- Cg) ≤ Cg + (- Cg)
    negBelowZeroRaw = ℚP.+-monoʳ-≤ (- Cg) CgNN

    negBelowZero : - Cg ≤ 0ℚ
    negBelowZero =
      subst
        (λ left → left ≤ 0ℚ)
        (ℚP.+-identityˡ (- Cg))
        (subst
          (λ right → 0ℚ + (- Cg) ≤ right)
          (ℚRing.solve-∀ Cg)
          negBelowZeroRaw)

    shifted : b + (- Cg) ≤ b + 0ℚ
    shifted = ℚP.+-monoʳ-≤ b negBelowZero
  in
  subst
    (λ left → left ≤ b)
    (ℚRing.solve-∀ b Cg)
    (subst
      (λ right → b + (- Cg) ≤ right)
      (ℚP.+-identityʳ b)
      shifted)

localDerivativeTubeBound :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  localDerivative dataSet * tubeWidth dataSet
  ≤ localDerivative dataSet * couplingCap dataSet
localDerivativeTubeBound dataSet =
  Norm.scaleNonnegative
    (localDerivative dataSet)
    (localDerivativeNonnegative dataSet)
    (tubeWidthBelowCap dataSet)

historyBudgetBound :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  betaMargin dataSet * historyConstant dataSet
  ≤ gaussianFloor dataSet * historySlope dataSet * couplingCap dataSet
historyBudgetBound dataSet =
  let
    first :
      betaMargin dataSet * historyConstant dataSet
      ≤ gaussianFloor dataSet * historyConstant dataSet
    first = scaleRightNonnegative
      (historyConstantNonnegative dataSet)
      (betaMarginBelowGaussian dataSet)

    bNN = ℚP.<⇒≤ (gaussianFloorPositive dataSet)
    second :
      gaussianFloor dataSet * historyConstant dataSet
      ≤ gaussianFloor dataSet
          * (historySlope dataSet * couplingCap dataSet)
    second = Norm.scaleNonnegative
      (gaussianFloor dataSet) bNN
      (historyBelowSlopeTimesCap dataSet)
  in
  ℚP.≤-trans first
    (subst
      (λ right →
        gaussianFloor dataSet * historyConstant dataSet ≤ right)
      (ℚRing.solve-∀
        (gaussianFloor dataSet)
        (historySlope dataSet)
        (couplingCap dataSet))
      second)

localPlusHistoryBelowCapBudget :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  localDerivative dataSet * tubeWidth dataSet
    + betaMargin dataSet * historyConstant dataSet
  ≤ (localDerivative dataSet + gaussianFloor dataSet * historySlope dataSet)
      * couplingCap dataSet
localPlusHistoryBelowCapBudget dataSet =
  let
    added = ℚP.+-mono-≤
      (localDerivativeTubeBound dataSet)
      (historyBudgetBound dataSet)
  in
  subst
    (λ right →
      localDerivative dataSet * tubeWidth dataSet
        + betaMargin dataSet * historyConstant dataSet ≤ right)
    (ℚRing.solve-∀
      (localDerivative dataSet)
      (gaussianFloor dataSet)
      (historySlope dataSet)
      (couplingCap dataSet))
    added

capBudgetBelowBetaMargin :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  (localDerivative dataSet + gaussianFloor dataSet * historySlope dataSet)
      * couplingCap dataSet
  < betaMargin dataSet
capBudgetBelowBetaMargin dataSet =
  let
    C = interactionConstant dataSet
    L = localDerivative dataSet
    b = gaussianFloor dataSet
    H = historySlope dataSet
    g = couplingCap dataSet
    combined = combinedSmallness dataSet
    shifted = ℚP.+-monoʳ-< (-(C * g)) combined
  in
  subst
    (λ left → left < betaMargin dataSet)
    (ℚRing.solve-∀ C L b H g)
    (subst
      (λ right →
        ((C + L + b * H) * g) + (-(C * g)) < right)
      (ℚRing.solve-∀ b C g)
      shifted)

augmentedHistoryGate :
  (dataSet : AugmentedHistorySmallCouplingGate) →
  localDerivative dataSet * tubeWidth dataSet
    + betaMargin dataSet * historyConstant dataSet
  < betaMargin dataSet
augmentedHistoryGate dataSet =
  ℚP.≤-<-trans
    (localPlusHistoryBelowCapBudget dataSet)
    (capBudgetBelowBetaMargin dataSet)

rowAHistorySuppressedCombinedSmallnessLevel : ProofLevel
rowAHistorySuppressedCombinedSmallnessLevel = machineChecked

rowAHistorySuppressedAugmentedGateLevel : ProofLevel
rowAHistorySuppressedAugmentedGateLevel = machineChecked

literalRowAHistorySensitivityLinearInCouplingLevel : ProofLevel
literalRowAHistorySensitivityLinearInCouplingLevel = conditional
