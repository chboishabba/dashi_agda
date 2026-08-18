module DASHI.Core.RobustObserverSeparationMarginExact where

------------------------------------------------------------------------
-- ROBUST NUMERIC SEPARATION UNDER LATER BOUNDED REFINEMENT
--
-- Cross-pollination calibration:
--
-- Tosio Kato, "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- The Kato citation motivates the generic pattern "reference gap minus bounded
-- perturbation remains a gap".  The theorem below is elementary ordered
-- rational arithmetic and is not a claim about spectra or operators.
--
-- If two reference observer values are separated by margin m, and later
-- refinement can move EACH endpoint by at most epsilon toward the other, then
-- the later values retain margin m - 2 epsilon.  Hence 2 epsilon < m is an
-- exact stopping certificate for a demonstrated split.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

record RobustSeparatorMarginData : Set where
  constructor robustSeparatorMarginData
  field
    referenceLeft referenceRight : ℚ
    futureLeft futureRight : ℚ
    referenceMargin endpointLoss : ℚ

    referenceSeparated :
      referenceLeft + referenceMargin ≤ referenceRight

    futureLeftUpper :
      futureLeft ≤ referenceLeft + endpointLoss

    futureRightLower :
      referenceRight - endpointLoss ≤ futureRight

open RobustSeparatorMarginData public

survivingMargin : RobustSeparatorMarginData → ℚ
survivingMargin dataSet =
  referenceMargin dataSet - (endpointLoss dataSet + endpointLoss dataSet)

robustSeparatorLower :
  (dataSet : RobustSeparatorMarginData) →
  futureLeft dataSet + survivingMargin dataSet ≤ futureRight dataSet
robustSeparatorLower dataSet =
  let
    l0 = referenceLeft dataSet
    r0 = referenceRight dataSet
    l1 = futureLeft dataSet
    r1 = futureRight dataSet
    m = referenceMargin dataSet
    e = endpointLoss dataSet

    firstRaw :
      l1 + (m - (e + e))
      ≤ (l0 + e) + (m - (e + e))
    firstRaw =
      ℚP.+-mono-≤
        (futureLeftUpper dataSet)
        ℚP.≤-refl

    firstTarget :
      (l0 + e) + (m - (e + e)) ≡ (l0 + m) - e
    firstTarget = ℚRing.solve-∀ l0 m e

    first :
      l1 + (m - (e + e)) ≤ (l0 + m) - e
    first =
      subst
        (λ upper → l1 + (m - (e + e)) ≤ upper)
        firstTarget
        firstRaw

    middleRaw :
      (- e) + (l0 + m) ≤ (- e) + r0
    middleRaw =
      ℚP.+-monoˡ-≤ (- e) (referenceSeparated dataSet)

    middleLeft : (- e) + (l0 + m) ≡ (l0 + m) - e
    middleLeft = ℚRing.solve-∀ l0 m e

    middleRight : (- e) + r0 ≡ r0 - e
    middleRight = ℚRing.solve-∀ r0 e

    middle : (l0 + m) - e ≤ r0 - e
    middle =
      subst
        (λ lower → lower ≤ r0 - e)
        middleLeft
        (subst
          (λ upper → (- e) + (l0 + m) ≤ upper)
          middleRight
          middleRaw)
  in
  ℚP.≤-trans first
    (ℚP.≤-trans middle (futureRightLower dataSet))

differencePositive : ∀ larger smaller →
  smaller < larger → 0ℚ < larger - smaller
differencePositive larger smaller smaller<larger =
  let
    left : ℚ
    left = - larger + larger
    right : ℚ
    right = - smaller + larger
    step : left < right
    step = ℚP.+-monoˡ-< larger
      (ℚP.neg-antimono-< smaller<larger)
    leftExact : left ≡ 0ℚ
    leftExact = ℚRing.solve-∀ larger
    rightExact : right ≡ larger - smaller
    rightExact = ℚRing.solve-∀ larger smaller
  in
  subst (λ selectedLeft → selectedLeft < larger - smaller)
    leftExact
    (subst (λ selectedRight → left < selectedRight)
      rightExact step)

strictEndpointBudgetLeavesPositiveMargin :
  (dataSet : RobustSeparatorMarginData) →
  endpointLoss dataSet + endpointLoss dataSet
    < referenceMargin dataSet →
  0ℚ < survivingMargin dataSet
strictEndpointBudgetLeavesPositiveMargin dataSet strict =
  differencePositive
    (referenceMargin dataSet)
    (endpointLoss dataSet + endpointLoss dataSet)
    strict

record RobustStrictSeparator : Set where
  constructor robustStrictSeparator
  field
    dataSet : RobustSeparatorMarginData
    endpointBudgetStrict :
      endpointLoss dataSet + endpointLoss dataSet
      < referenceMargin dataSet

open RobustStrictSeparator public

robustStrictSeparatorPositiveMargin :
  (witness : RobustStrictSeparator) →
  0ℚ < survivingMargin (dataSet witness)
robustStrictSeparatorPositiveMargin witness =
  strictEndpointBudgetLeavesPositiveMargin
    (dataSet witness)
    (endpointBudgetStrict witness)

robustStrictSeparatorFutureLower :
  (witness : RobustStrictSeparator) →
  futureLeft (dataSet witness)
    + survivingMargin (dataSet witness)
  ≤ futureRight (dataSet witness)
robustStrictSeparatorFutureLower witness =
  robustSeparatorLower (dataSet witness)

record RobustObserverSeparationBoundary : Set where
  constructor robustObserverSeparationBoundary
  field
    twoEndpointLossesAreCharged : Bool
    twoEndpointLossesAreChargedIsTrue :
      twoEndpointLossesAreCharged ≡ true
    strictTwoEndpointBudgetCertifiesPersistentSplit : Bool
    strictTwoEndpointBudgetCertifiesPersistentSplitIsTrue :
      strictTwoEndpointBudgetCertifiesPersistentSplit ≡ true
    boundedRefinementAutomaticallyMeansExactStateRecovery : Bool
    boundedRefinementAutomaticallyMeansExactStateRecoveryIsFalse :
      boundedRefinementAutomaticallyMeansExactStateRecovery ≡ false
    numericSeparationAutomaticallyGrantsSemanticAuthority : Bool
    numericSeparationAutomaticallyGrantsSemanticAuthorityIsFalse :
      numericSeparationAutomaticallyGrantsSemanticAuthority ≡ false

canonicalRobustObserverSeparationBoundary :
  RobustObserverSeparationBoundary
canonicalRobustObserverSeparationBoundary =
  robustObserverSeparationBoundary
    true refl
    true refl
    false refl
    false refl
