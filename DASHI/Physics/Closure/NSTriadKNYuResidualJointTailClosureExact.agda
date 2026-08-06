module DASHI.Physics.Closure.NSTriadKNYuResidualJointTailClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Connect the three round-fourteen source-tail criteria to the already-proved
-- epsilon/3 surplus theorem.  A single terminal cutoff controls:
--
-- * the normalized exterior source tail;
-- * the derivative-compatible increment-defect tail; and
-- * the complete post-absorption localization tail.
--
-- The pointwise exterior and commutator domination theorems then yield the
-- exact JointResidualVanishing record required by Yu's finite surplus transfer.
-- No residual class is discarded and no source tail is inferred from energy.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNYuExteriorTailCriterionExact as Exterior
import DASHI.Physics.Closure.NSTriadKNYuIncrementDefectTailCriterionExact as Increment
import DASHI.Physics.Closure.NSTriadKNYuLocalizationTailCriterionExact as Localization
import DASHI.Physics.Closure.NSTriadKNYuFiniteSurplusVanishingTransferExact as Yu
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record YuResidualJointTailData : Set₁ where
  constructor yu-residual-joint-tail-data
  field
    surplusData : Yu.ThreeResidualSurplusData
    exteriorData : Exterior.ExteriorTailCriterionData
    incrementData : Increment.IncrementDefectTailData
    localizationData : Localization.LocalizationTailData

    farFieldMeaning :
      (shell : ℕ) →
      Yu.farField surplusData shell
      ≡ Exterior.exteriorResidual exteriorData shell

    commutatorMeaning :
      (shell : ℕ) →
      Yu.commutatorEnvelope surplusData shell
      ≡ Increment.commutatorTail incrementData shell

    localizationMeaning :
      (shell : ℕ) →
      Yu.localization surplusData shell
      ≡ Localization.localizationTail localizationData shell

    commonTail :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      ℕ

    exteriorSourceTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      Exterior.sourceTail exteriorData shell ≤ Yu.oneThird * epsilon

    incrementDefectTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      Increment.incrementDefectTail incrementData shell
      ≤ Yu.oneThird * epsilon

    localizationResidualTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      Localization.localizationTail localizationData shell
      ≤ Yu.oneThird * epsilon

open YuResidualJointTailData public

jointResidualVanishing :
  (dataSet : YuResidualJointTailData) →
  Yu.JointResidualVanishing (surplusData dataSet)
jointResidualVanishing dataSet =
  Yu.joint-residual-vanishing
    (commonTail dataSet)
    farBound
    commutatorBound
    localizationBound
  where
  farBound :
    (epsilon : ℚ) →
    (epsilonPositive : 0ℚ < epsilon) →
    (shell : ℕ) →
    commonTail dataSet epsilon epsilonPositive ≤ shell →
    Yu.farField (surplusData dataSet) shell
    ≤ Yu.oneThird * epsilon
  farBound epsilon epsilonPositive shell cutoffBelowShell =
    subst
      (λ residual → residual ≤ Yu.oneThird * epsilon)
      (sym (farFieldMeaning dataSet shell))
      (ℚₚ.≤-trans
        (Exterior.exteriorResidualPointwiseBySource
          (exteriorData dataSet) shell)
        (exteriorSourceTailBound
          dataSet epsilon epsilonPositive shell cutoffBelowShell))

  commutatorBound :
    (epsilon : ℚ) →
    (epsilonPositive : 0ℚ < epsilon) →
    (shell : ℕ) →
    commonTail dataSet epsilon epsilonPositive ≤ shell →
    Yu.commutatorEnvelope (surplusData dataSet) shell
    ≤ Yu.oneThird * epsilon
  commutatorBound epsilon epsilonPositive shell cutoffBelowShell =
    subst
      (λ residual → residual ≤ Yu.oneThird * epsilon)
      (sym (commutatorMeaning dataSet shell))
      (ℚₚ.≤-trans
        (Increment.commutatorByIncrementDefect
          (incrementData dataSet) shell)
        (incrementDefectTailBound
          dataSet epsilon epsilonPositive shell cutoffBelowShell))

  localizationBound :
    (epsilon : ℚ) →
    (epsilonPositive : 0ℚ < epsilon) →
    (shell : ℕ) →
    commonTail dataSet epsilon epsilonPositive ≤ shell →
    Yu.localization (surplusData dataSet) shell
    ≤ Yu.oneThird * epsilon
  localizationBound epsilon epsilonPositive shell cutoffBelowShell =
    subst
      (λ residual → residual ≤ Yu.oneThird * epsilon)
      (sym (localizationMeaning dataSet shell))
      (localizationResidualTailBound
        dataSet epsilon epsilonPositive shell cutoffBelowShell)

yuResidualSurplusVanishing :
  (dataSet : YuResidualJointTailData) →
  Limit.TendsToZero (Yu.surplus (surplusData dataSet))
yuResidualSurplusVanishing dataSet =
  Yu.surplusVanishingFromResidualVanishing
    (surplusData dataSet)
    (jointResidualVanishing dataSet)
