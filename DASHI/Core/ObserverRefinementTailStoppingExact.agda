module DASHI.Core.ObserverRefinementTailStoppingExact where

------------------------------------------------------------------------
-- STOPPING CERTIFICATE FOR A SUMMABLY / UNIFORMLY BOUNDED REFINEMENT TAIL
--
-- Once a current split has margin m and ALL remaining future refinement can
-- move each endpoint by at most E, the generic robust-separation theorem gives
-- a persistent margin m - 2E at every later stage.  Therefore 2E < m is a
-- stopping rule: no later admissible refinement covered by the tail bound can
-- erase the demonstrated split.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_; _<_)

import DASHI.Core.RobustObserverSeparationMarginExact as Robust

record RefinementTailSeparatorData : Set where
  constructor refinementTailSeparatorData
  field
    referenceLeft referenceRight : ℚ
    referenceMargin remainingEndpointTail : ℚ

    futureLeft futureRight : Nat → ℚ

    referenceSeparated :
      referenceLeft + referenceMargin ≤ referenceRight

    everyFutureLeftUpper :
      (laterStage : Nat) →
      futureLeft laterStage ≤ referenceLeft + remainingEndpointTail

    everyFutureRightLower :
      (laterStage : Nat) →
      referenceRight - remainingEndpointTail ≤ futureRight laterStage

open RefinementTailSeparatorData public

stageRobustData :
  (dataSet : RefinementTailSeparatorData) →
  Nat → Robust.RobustSeparatorMarginData
stageRobustData dataSet laterStage =
  Robust.robustSeparatorMarginData
    (referenceLeft dataSet)
    (referenceRight dataSet)
    (futureLeft dataSet laterStage)
    (futureRight dataSet laterStage)
    (referenceMargin dataSet)
    (remainingEndpointTail dataSet)
    (referenceSeparated dataSet)
    (everyFutureLeftUpper dataSet laterStage)
    (everyFutureRightLower dataSet laterStage)

persistentFutureMarginLower :
  (dataSet : RefinementTailSeparatorData) →
  (laterStage : Nat) →
  futureLeft dataSet laterStage
    + Robust.survivingMargin (stageRobustData dataSet laterStage)
  ≤ futureRight dataSet laterStage
persistentFutureMarginLower dataSet laterStage =
  Robust.robustSeparatorLower (stageRobustData dataSet laterStage)

record RefinementTailStoppingCertificate
    (dataSet : RefinementTailSeparatorData) : Set where
  constructor refinementTailStoppingCertificate
  field
    totalTwoEndpointTailStrict :
      remainingEndpointTail dataSet + remainingEndpointTail dataSet
      < referenceMargin dataSet

open RefinementTailStoppingCertificate public

stoppingCertificateKeepsEveryFutureMarginPositive :
  (dataSet : RefinementTailSeparatorData) →
  RefinementTailStoppingCertificate dataSet →
  (laterStage : Nat) →
  0ℚ < Robust.survivingMargin (stageRobustData dataSet laterStage)
stoppingCertificateKeepsEveryFutureMarginPositive dataSet certificate laterStage =
  Robust.strictEndpointBudgetLeavesPositiveMargin
    (stageRobustData dataSet laterStage)
    (totalTwoEndpointTailStrict certificate)

record ObserverRefinementTailStoppingBoundary : Set where
  constructor observerRefinementTailStoppingBoundary
  field
    currentSplitPlusTailBoundCanCertifyPermanentSplit : Bool
    currentSplitPlusTailBoundCanCertifyPermanentSplitIsTrue :
      currentSplitPlusTailBoundCanCertifyPermanentSplit ≡ true
    stoppingRuleRequiresTwoEndpointBudget : Bool
    stoppingRuleRequiresTwoEndpointBudgetIsTrue :
      stoppingRuleRequiresTwoEndpointBudget ≡ true
    stoppingRuleMeansNoFurtherObserversCanEverMatter : Bool
    stoppingRuleMeansNoFurtherObserversCanEverMatterIsFalse :
      stoppingRuleMeansNoFurtherObserversCanEverMatter ≡ false
    stoppingRuleOnlyProtectsDemonstratedSplit : Bool
    stoppingRuleOnlyProtectsDemonstratedSplitIsTrue :
      stoppingRuleOnlyProtectsDemonstratedSplit ≡ true

canonicalObserverRefinementTailStoppingBoundary :
  ObserverRefinementTailStoppingBoundary
canonicalObserverRefinementTailStoppingBoundary =
  observerRefinementTailStoppingBoundary
    true refl
    true refl
    false refl
    true refl
