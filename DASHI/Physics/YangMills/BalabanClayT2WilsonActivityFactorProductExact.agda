module DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _/_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

------------------------------------------------------------------------
-- The literal absolute activity is factored into the six physical owners.
-- Once every owner is bounded in the common polymer norm and their certified
-- product is at most 1/16, the decisive traversal theorem follows.
--
-- Sign convention: every factor is an absolute-value majorant and therefore
-- nonnegative.  The nonnegativity witnesses enter every product-monotonicity
-- step explicitly; no signed activity and no false globally monotone
-- multiplication law can enter the certificate.
--
-- Cluster-expansion references used by the downstream criterion comparison:
--
-- R. Kotecký and D. Preiss,
-- "Cluster expansion for abstract polymer models",
-- DOI: 10.1007/BF01211762
--
-- R. Fernández and A. Procacci,
-- "Cluster expansion for abstract polymer models. New bounds from an old
-- approach",
-- DOI: 10.1007/s00220-007-0279-2
------------------------------------------------------------------------

record WilsonTraversalActivityFactors (Scale Traversal : Set) : Set₁ where
  field
    activity : Scale → Traversal → ℚ

    actionFactor jacobianFactor determinantFactor bchFactor
      localizationFactor patchFactor : Scale → Traversal → ℚ

    actionUpper jacobianUpper determinantUpper bchUpper
      localizationUpper patchUpper : ℚ

    activityNonnegative : ∀ scale traversal →
      0ℚ ≤ activity scale traversal
    actionFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ actionFactor scale traversal
    jacobianFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ jacobianFactor scale traversal
    determinantFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ determinantFactor scale traversal
    bchFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ bchFactor scale traversal
    localizationFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ localizationFactor scale traversal
    patchFactorNonnegative : ∀ scale traversal →
      0ℚ ≤ patchFactor scale traversal

    actionUpperNonnegative : 0ℚ ≤ actionUpper
    jacobianUpperNonnegative : 0ℚ ≤ jacobianUpper
    determinantUpperNonnegative : 0ℚ ≤ determinantUpper
    bchUpperNonnegative : 0ℚ ≤ bchUpper
    localizationUpperNonnegative : 0ℚ ≤ localizationUpper
    patchUpperNonnegative : 0ℚ ≤ patchUpper

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right

    multiplyNonnegative : ∀ {left right} →
      0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right

    multiplyMonotoneNonnegative :
      ∀ {left leftUpper right rightUpper} →
      0ℚ ≤ left → 0ℚ ≤ leftUpper →
      0ℚ ≤ right → 0ℚ ≤ rightUpper →
      left ≤ leftUpper → right ≤ rightUpper →
      left * right ≤ leftUpper * rightUpper

    activityBelowPhysicalProduct : ∀ scale traversal →
      activity scale traversal
      ≤ actionFactor scale traversal
        * (jacobianFactor scale traversal
        * (determinantFactor scale traversal
        * (bchFactor scale traversal
        * (localizationFactor scale traversal
        * patchFactor scale traversal))))

    actionControlled : ∀ scale traversal →
      actionFactor scale traversal ≤ actionUpper
    jacobianControlled : ∀ scale traversal →
      jacobianFactor scale traversal ≤ jacobianUpper
    determinantControlled : ∀ scale traversal →
      determinantFactor scale traversal ≤ determinantUpper
    bchControlled : ∀ scale traversal →
      bchFactor scale traversal ≤ bchUpper
    localizationControlled : ∀ scale traversal →
      localizationFactor scale traversal ≤ localizationUpper
    patchControlled : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper

    certifiedProductExact :
      actionUpper
        * (jacobianUpper
        * (determinantUpper
        * (bchUpper
        * (localizationUpper * patchUpper))))
      ≡ oneSixteenth

open WilsonTraversalActivityFactors public

physicalLocalizationPatchNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  0ℚ ≤ localizationFactor dataSet scale traversal
    * patchFactor dataSet scale traversal
physicalLocalizationPatchNonnegative dataSet scale traversal =
  multiplyNonnegative dataSet
    (localizationFactorNonnegative dataSet scale traversal)
    (patchFactorNonnegative dataSet scale traversal)

upperLocalizationPatchNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal) →
  0ℚ ≤ localizationUpper dataSet * patchUpper dataSet
upperLocalizationPatchNonnegative dataSet =
  multiplyNonnegative dataSet
    (localizationUpperNonnegative dataSet)
    (patchUpperNonnegative dataSet)

physicalBCHTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  0ℚ ≤ bchFactor dataSet scale traversal
    * (localizationFactor dataSet scale traversal
      * patchFactor dataSet scale traversal)
physicalBCHTailNonnegative dataSet scale traversal =
  multiplyNonnegative dataSet
    (bchFactorNonnegative dataSet scale traversal)
    (physicalLocalizationPatchNonnegative dataSet scale traversal)

upperBCHTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal) →
  0ℚ ≤ bchUpper dataSet
    * (localizationUpper dataSet * patchUpper dataSet)
upperBCHTailNonnegative dataSet =
  multiplyNonnegative dataSet
    (bchUpperNonnegative dataSet)
    (upperLocalizationPatchNonnegative dataSet)

physicalDeterminantTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  0ℚ ≤ determinantFactor dataSet scale traversal
    * (bchFactor dataSet scale traversal
      * (localizationFactor dataSet scale traversal
        * patchFactor dataSet scale traversal))
physicalDeterminantTailNonnegative dataSet scale traversal =
  multiplyNonnegative dataSet
    (determinantFactorNonnegative dataSet scale traversal)
    (physicalBCHTailNonnegative dataSet scale traversal)

upperDeterminantTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal) →
  0ℚ ≤ determinantUpper dataSet
    * (bchUpper dataSet
      * (localizationUpper dataSet * patchUpper dataSet))
upperDeterminantTailNonnegative dataSet =
  multiplyNonnegative dataSet
    (determinantUpperNonnegative dataSet)
    (upperBCHTailNonnegative dataSet)

physicalJacobianTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  0ℚ ≤ jacobianFactor dataSet scale traversal
    * (determinantFactor dataSet scale traversal
      * (bchFactor dataSet scale traversal
        * (localizationFactor dataSet scale traversal
          * patchFactor dataSet scale traversal)))
physicalJacobianTailNonnegative dataSet scale traversal =
  multiplyNonnegative dataSet
    (jacobianFactorNonnegative dataSet scale traversal)
    (physicalDeterminantTailNonnegative dataSet scale traversal)

upperJacobianTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal) →
  0ℚ ≤ jacobianUpper dataSet
    * (determinantUpper dataSet
      * (bchUpper dataSet
        * (localizationUpper dataSet * patchUpper dataSet)))
upperJacobianTailNonnegative dataSet =
  multiplyNonnegative dataSet
    (jacobianUpperNonnegative dataSet)
    (upperDeterminantTailNonnegative dataSet)

physicalProductBelowCertifiedProduct :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  actionFactor dataSet scale traversal
    * (jacobianFactor dataSet scale traversal
    * (determinantFactor dataSet scale traversal
    * (bchFactor dataSet scale traversal
    * (localizationFactor dataSet scale traversal
    * patchFactor dataSet scale traversal))))
  ≤ actionUpper dataSet
    * (jacobianUpper dataSet
    * (determinantUpper dataSet
    * (bchUpper dataSet
    * (localizationUpper dataSet * patchUpper dataSet))))
physicalProductBelowCertifiedProduct dataSet scale traversal =
  multiplyMonotoneNonnegative dataSet
    (actionFactorNonnegative dataSet scale traversal)
    (actionUpperNonnegative dataSet)
    (physicalJacobianTailNonnegative dataSet scale traversal)
    (upperJacobianTailNonnegative dataSet)
    (actionControlled dataSet scale traversal)
    (multiplyMonotoneNonnegative dataSet
      (jacobianFactorNonnegative dataSet scale traversal)
      (jacobianUpperNonnegative dataSet)
      (physicalDeterminantTailNonnegative dataSet scale traversal)
      (upperDeterminantTailNonnegative dataSet)
      (jacobianControlled dataSet scale traversal)
      (multiplyMonotoneNonnegative dataSet
        (determinantFactorNonnegative dataSet scale traversal)
        (determinantUpperNonnegative dataSet)
        (physicalBCHTailNonnegative dataSet scale traversal)
        (upperBCHTailNonnegative dataSet)
        (determinantControlled dataSet scale traversal)
        (multiplyMonotoneNonnegative dataSet
          (bchFactorNonnegative dataSet scale traversal)
          (bchUpperNonnegative dataSet)
          (physicalLocalizationPatchNonnegative dataSet scale traversal)
          (upperLocalizationPatchNonnegative dataSet)
          (bchControlled dataSet scale traversal)
          (multiplyMonotoneNonnegative dataSet
            (localizationFactorNonnegative dataSet scale traversal)
            (localizationUpperNonnegative dataSet)
            (patchFactorNonnegative dataSet scale traversal)
            (patchUpperNonnegative dataSet)
            (localizationControlled dataSet scale traversal)
            (patchControlled dataSet scale traversal)))))

wilsonActivityPerTraversalBelowOneSixteenth :
  ∀ {Scale Traversal}
    (dataSet : WilsonTraversalActivityFactors Scale Traversal)
    scale traversal →
  activity dataSet scale traversal ≤ oneSixteenth
wilsonActivityPerTraversalBelowOneSixteenth dataSet scale traversal =
  subst
    (λ upper → activity dataSet scale traversal ≤ upper)
    (certifiedProductExact dataSet)
    (transitive dataSet
      (activityBelowPhysicalProduct dataSet scale traversal)
      (physicalProductBelowCertifiedProduct dataSet scale traversal))

wilsonActivityFactorCombinationLevel : ProofLevel
wilsonActivityFactorCombinationLevel = machineChecked

wilsonActivityPerTraversalTheoremLevel : ProofLevel
wilsonActivityPerTraversalTheoremLevel = machineChecked

wilsonActivityAbsoluteSignConventionLevel : ProofLevel
wilsonActivityAbsoluteSignConventionLevel = machineChecked

record LiteralTraversalLossLedger : Set where
  field
    actionGain : ℚ
    jacobianLoss determinantLoss bchLoss localizationLoss patchLoss : ℚ
    logSixteen : ℚ
    netGainSufficient :
      actionGain - (jacobianLoss + (determinantLoss + (bchLoss + (localizationLoss + patchLoss))))
      ≡ logSixteen

open LiteralTraversalLossLedger public

literalTraversalLossLedgerLevel : ProofLevel
literalTraversalLossLedgerLevel = machineChecked

-- The remaining physical estimates are exactly the six nonnegative component
-- bounds in the common norm, plus duplicate-free traversal assignment.
literalWilsonSixFactorBoundsLevel : ProofLevel
literalWilsonSixFactorBoundsLevel = conditional
