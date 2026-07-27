module DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _≤_; _/_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

------------------------------------------------------------------------
-- The literal activity is factored into the six physical owners.  Once every
-- owner is bounded in the common polymer norm and their certified product is
-- at most 1/16, the decisive traversal theorem follows mechanically.
------------------------------------------------------------------------

record WilsonTraversalActivityFactors (Scale Traversal : Set) : Set₁ where
  field
    activity : Scale → Traversal → ℚ

    actionFactor jacobianFactor determinantFactor bchFactor
      localizationFactor patchFactor : Scale → Traversal → ℚ

    actionUpper jacobianUpper determinantUpper bchUpper
      localizationUpper patchUpper : ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
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
  multiplyMonotone dataSet
    (actionControlled dataSet scale traversal)
    (multiplyMonotone dataSet
      (jacobianControlled dataSet scale traversal)
      (multiplyMonotone dataSet
        (determinantControlled dataSet scale traversal)
        (multiplyMonotone dataSet
          (bchControlled dataSet scale traversal)
          (multiplyMonotone dataSet
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

-- The remaining physical estimates are now exactly the six component bounds,
-- all in the common norm; there is no additional shell or KP mystery after
-- those bounds and the duplicate-free traversal assignment are inhabited.
literalWilsonSixFactorBoundsLevel : ProofLevel
literalWilsonSixFactorBoundsLevel = conditional
