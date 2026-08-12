module DASHI.Physics.Closure.NSTriadKNMixedCriticalYoungSoftRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Formalize the pre-absorption endpoint requested for Com and kernel.  If a
-- physical owner reaches
--
--   P <= x y + A,
--   x^2 <= D,
--   y^2 <= C X,
--
-- then the repository's already-proved scaled Young inequality gives, for
-- EVERY positive rational epsilon,
--
--   P <= epsilon D + A + (epsilon^{-1}/4) C X.
--
-- Hence the owner is Young-soft and contributes no hard viscosity floor.  This
-- theorem is mechanism-level: Com/kernel only become soft after their genuine
-- physical estimates instantiate this mixed endpoint.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoBadExcursionYoungAbsorptionExact as Young
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

quarter : ℚ
quarter = Int.+ 1 / 4

quarterYoungFromSplit :
  Threshold.PositiveThreshold → Young.QuarterYoungParameter
quarterYoungFromSplit split = record
  { epsilon = Threshold.threshold split
  ; quarterInverse = quarter * Threshold.thresholdInverse split
  ; epsilonNonnegative = Threshold.thresholdNonnegative split
  ; quarterInverseNonnegative = quarterInverseNN
  ; quarterInverseLaw = quarterInverseLaw
  }
  where
  quarterNN : 0ℚ ≤ quarter
  quarterNN = ℚP.<⇒≤ (ℚP.positive⁻¹ quarter)

  quarterInverseNN :
    0ℚ ≤ quarter * Threshold.thresholdInverse split
  quarterInverseNN =
    let instance
      quarterNNI = nonNegative quarterNN
      inverseNNI = nonNegative (Threshold.thresholdInverseNonnegative split)
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          quarter (Threshold.thresholdInverse split)
    in ℚP.nonNegative⁻¹
      (quarter * Threshold.thresholdInverse split)

  quarterInverseLaw :
    4 * Threshold.threshold split
      * (quarter * Threshold.thresholdInverse split) ≡ 1ℚ
  quarterInverseLaw
    rewrite Threshold.inverseMeaning split = solve []

record MixedCriticalPreAbsorption
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set where
  field
    production leftFactor rightFactor dataRemainder baseCriticalCoefficient : ℚ

    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    criticalNonnegative : 0ℚ ≤ Owner.integralCritical environment
    baseCriticalCoefficientNonnegative : 0ℚ ≤ baseCriticalCoefficient

    productionBelowMixed :
      production ≤ leftFactor * rightFactor + dataRemainder

    leftSquareBelowDissipation :
      L2.square leftFactor ≤ Owner.dissipation environment

    rightSquareBelowCritical :
      L2.square rightFactor
      ≤ baseCriticalCoefficient * Owner.integralCritical environment

open MixedCriticalPreAbsorption public

criticalCoefficientAtSplit :
  ∀ {environment selectedOwner} →
  MixedCriticalPreAbsorption environment selectedOwner →
  Threshold.PositiveThreshold → ℚ
criticalCoefficientAtSplit producer split =
  quarter * Threshold.thresholdInverse split
    * baseCriticalCoefficient producer

mixedCriticalOwnerAtSplit :
  ∀ {environment selectedOwner} →
  MixedCriticalPreAbsorption environment selectedOwner →
  Threshold.PositiveThreshold →
  Owner.AdmissibleOwnerEstimate environment
mixedCriticalOwnerAtSplit {environment} {selectedOwner} producer split =
  Owner.admissible-owner-estimate
    selectedOwner
    (production producer)
    (Threshold.threshold split)
    (dataRemainder producer)
    (criticalCoefficientAtSplit producer split)
    ownerBound
  where
  youngParameter = quarterYoungFromSplit split

  youngProduct :
    leftFactor producer * rightFactor producer
    ≤ Threshold.threshold split * L2.square (leftFactor producer)
      + (quarter * Threshold.thresholdInverse split)
        * L2.square (rightFactor producer)
  youngProduct =
    Young.scaledYoungProductBound
      youngParameter (leftFactor producer) (rightFactor producer)

  leftScaled :
    Threshold.threshold split * L2.square (leftFactor producer)
    ≤ Threshold.threshold split * Owner.dissipation environment
  leftScaled =
    let instance epsilonNNI = nonNegative (Threshold.thresholdNonnegative split)
    in ℚP.*-monoˡ-≤-nonNeg
      (Threshold.threshold split)
      (leftSquareBelowDissipation producer)

  quarterInverseNN :
    0ℚ ≤ quarter * Threshold.thresholdInverse split
  quarterInverseNN = Young.quarterInverseNonnegative youngParameter

  rightScaled :
    (quarter * Threshold.thresholdInverse split)
      * L2.square (rightFactor producer)
    ≤ (quarter * Threshold.thresholdInverse split)
      * (baseCriticalCoefficient producer
        * Owner.integralCritical environment)
  rightScaled =
    let instance qNNI = nonNegative quarterInverseNN
    in ℚP.*-monoˡ-≤-nonNeg
      (quarter * Threshold.thresholdInverse split)
      (rightSquareBelowCritical producer)

  mixedToBudget :
    leftFactor producer * rightFactor producer
    ≤ Threshold.threshold split * Owner.dissipation environment
      + (quarter * Threshold.thresholdInverse split)
        * (baseCriticalCoefficient producer
          * Owner.integralCritical environment)
  mixedToBudget =
    ℚP.≤-trans youngProduct
      (ℚP.+-mono-≤ leftScaled rightScaled)

  productionToBudgetPlusData :
    production producer
    ≤ Threshold.threshold split * Owner.dissipation environment
      + (quarter * Threshold.thresholdInverse split)
        * (baseCriticalCoefficient producer
          * Owner.integralCritical environment)
      + dataRemainder producer
  productionToBudgetPlusData =
    ℚP.≤-trans
      (productionBelowMixed producer)
      (ℚP.+-mono-≤ mixedToBudget ℚP.≤-refl)

  targetMeaning :
    Threshold.threshold split * Owner.dissipation environment
      + (quarter * Threshold.thresholdInverse split)
        * (baseCriticalCoefficient producer
          * Owner.integralCritical environment)
      + dataRemainder producer
    ≡ Threshold.threshold split * Owner.dissipation environment
      + dataRemainder producer
      + criticalCoefficientAtSplit producer split
        * Owner.integralCritical environment
  targetMeaning = solve
    ( Threshold.threshold split
    ∷ Owner.dissipation environment
    ∷ quarter
    ∷ Threshold.thresholdInverse split
    ∷ baseCriticalCoefficient producer
    ∷ Owner.integralCritical environment
    ∷ dataRemainder producer
    ∷ [])

  ownerBound =
    subst
      (production producer ≤_)
      targetMeaning
      productionToBudgetPlusData

mixedCriticalOwnerIdentity :
  ∀ {environment selectedOwner}
    (producer : MixedCriticalPreAbsorption environment selectedOwner)
    split →
  Owner.owner (mixedCriticalOwnerAtSplit producer split) ≡ selectedOwner
mixedCriticalOwnerIdentity producer split = refl

mixedCriticalEtaExact :
  ∀ {environment selectedOwner}
    (producer : MixedCriticalPreAbsorption environment selectedOwner)
    split →
  Owner.eta (mixedCriticalOwnerAtSplit producer split)
  ≡ Threshold.threshold split
mixedCriticalEtaExact producer split = refl

mixedCriticalYoungSoftFamily :
  ∀ {environment selectedOwner} →
  MixedCriticalPreAbsorption environment selectedOwner →
  Soft.YoungSoftOwnerFamily environment selectedOwner
mixedCriticalYoungSoftFamily producer = record
  { estimateAtSplit = mixedCriticalOwnerAtSplit producer
  ; ownerAtSplit = mixedCriticalOwnerIdentity producer
  ; etaAtSplit = mixedCriticalEtaExact producer
  }

comYoungSoftFromMixedEndpoint :
  ∀ {environment} →
  MixedCriticalPreAbsorption environment Tax.Com →
  Soft.YoungSoftOwnerFamily environment Tax.Com
comYoungSoftFromMixedEndpoint = mixedCriticalYoungSoftFamily

kernelYoungSoftFromMixedEndpoint :
  ∀ {environment} →
  MixedCriticalPreAbsorption environment Tax.kernel →
  Soft.YoungSoftOwnerFamily environment Tax.kernel
kernelYoungSoftFromMixedEndpoint = mixedCriticalYoungSoftFamily

mixedCriticalEndpointImpliesYoungSoft : Bool
mixedCriticalEndpointImpliesYoungSoft = true

mixedCriticalEndpointImpliesYoungSoftIsTrue :
  mixedCriticalEndpointImpliesYoungSoft ≡ true
mixedCriticalEndpointImpliesYoungSoftIsTrue = refl
