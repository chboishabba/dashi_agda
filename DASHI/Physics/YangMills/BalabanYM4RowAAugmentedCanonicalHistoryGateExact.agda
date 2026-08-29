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
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

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
    g = couplingCap dataSet

    bNN : 0ℚ ≤ b
    bNN = ℚP.<⇒≤ (gaussianFloorPositive dataSet)

    bHNN : 0ℚ ≤ b * H
    bHNN =
      let instance bNonnegative = ℚ.nonNegative bNN
          hNonnegative = ℚ.nonNegative (historySlopeNonnegative dataSet)
      in ℚP.nonNegative⁻¹ (b * H)

    cBelow : C ≤ C + L + b * H
    cBelow =
      ℚP.≤-trans
        (subst (λ right → C ≤ right)
          (ℚP.+-identityʳ C)
          (ℚP.+-monoʳ-≤ C (localDerivativeNonnegative dataSet)))
        (subst (λ left → C + L ≤ left)
          (ℚP.+-identityʳ (C + L))
          (ℚP.+-monoʳ-≤ (C + L) bHNN))
  in
  Norm.scaleʳ-nonNeg (couplingCapNonnegative dataSet) cBelow

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
    CgNN : 0ℚ ≤ interactionConstant dataSet * couplingCap dataSet
    CgNN =
      let instance cNN = ℚ.nonNegative (interactionConstantNonnegative dataSet)
          gNN = ℚ.nonNegative (couplingCapNonnegative dataSet)
      in ℚP.nonNegative⁻¹
        (interactionConstant dataSet * couplingCap dataSet)
  in
  subst
    (λ left → left ≤ gaussianFloor dataSet)
    (ℚRing.solve-∀
      (gaussianFloor dataSet)
      (interactionConstant dataSet * couplingCap dataSet))
    (ℚP.+-monoˡ-≤-nonNeg
      (gaussianFloor dataSet)
      (ℚP.neg-nonPos CgNN))

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
    marginNN : 0ℚ ≤ betaMargin dataSet
    marginNN = ℚP.<⇒≤ (betaMarginPositive dataSet)

    first :
      betaMargin dataSet * historyConstant dataSet
      ≤ gaussianFloor dataSet * historyConstant dataSet
    first = Norm.scaleʳ-nonNeg
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

-- Physical seam: prove the literal propagated irrelevant-history shooting
-- sensitivity satisfies q_history <= H gamma with finite source H.  Once that
-- O(gamma) response is identified, one source smallness choice pays both direct
-- and history sensitivity simultaneously.
literalRowAHistorySensitivityLinearInCouplingLevel : ProofLevel
literalRowAHistorySensitivityLinearInCouplingLevel = conditional
