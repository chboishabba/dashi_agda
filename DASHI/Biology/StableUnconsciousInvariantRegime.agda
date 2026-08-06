module DASHI.Biology.StableUnconsciousInvariantRegime where

open import DASHI.Core.Prelude

import DASHI.Biology.UnconsciousAccessRegime as Unconscious
import DASHI.Biology.SymbolicTransformWithoutHomunculus as Symbolic

------------------------------------------------------------------------
-- Stable access-blocked causal regime over a perturbation family.
--
-- Access remains below threshold for every finite perturbation while the
-- representation continues to alter action.  A transformed carrier may lower
-- access cost while preserving an invariant.  No personal diagnosis follows.

data LocalPerturbation : Set where
  baselinePerturbation : LocalPerturbation
  weakPerturbation : LocalPerturbation
  strongPerturbation : LocalPerturbation

accessLevel : LocalPerturbation → Bool → Nat
accessLevel baselinePerturbation representation = 0
accessLevel weakPerturbation representation = 0
accessLevel strongPerturbation representation = 1

accessThreshold : Nat
accessThreshold = 2

accessBlocked : LocalPerturbation → Bool → Bool
accessBlocked baselinePerturbation representation = true
accessBlocked weakPerturbation representation = true
accessBlocked strongPerturbation representation = true

actionInfluence : LocalPerturbation → Bool → Bool
actionInfluence perturbation representation = representation

stableBlockingAcrossPerturbations :
  (p : LocalPerturbation) →
  accessBlocked p true ≡ true
stableBlockingAcrossPerturbations baselinePerturbation = refl
stableBlockingAcrossPerturbations weakPerturbation = refl
stableBlockingAcrossPerturbations strongPerturbation = refl

blockedCarrierStillInfluencesAction :
  (p : LocalPerturbation) →
  actionInfluence p true ≡ actionInfluence p false → ⊥
blockedCarrierStillInfluencesAction baselinePerturbation ()
blockedCarrierStillInfluencesAction weakPerturbation ()
blockedCarrierStillInfluencesAction strongPerturbation ()

------------------------------------------------------------------------
-- Transformed access with invariant preservation.

directCarrier : Symbolic.SymbolForm
directCarrier = Symbolic.directRender true

transformedCarrier : Symbolic.SymbolForm
transformedCarrier = Symbolic.transformedRender true

carrierInvariantPreserved :
  Symbolic.symbolInvariant directCarrier
  ≡
  Symbolic.symbolInvariant transformedCarrier
carrierInvariantPreserved = refl

directCarrierAccessCost : Nat
directCarrierAccessCost = 3

transformedCarrierAccessCost : Nat
transformedCarrierAccessCost = 1

transformedCarrierCostLower :
  transformedCarrierAccessCost ≤ directCarrierAccessCost
transformedCarrierCostLower = s≤s z≤n

record StableUnconsciousWitness : Set₁ where
  constructor stableUnconsciousWitness
  field
    representation : Bool
    stableBlocked :
      (p : LocalPerturbation) →
      accessBlocked p representation ≡ true
    causallyEffective :
      (p : LocalPerturbation) →
      actionInfluence p representation
      ≡
      actionInfluence p false
      →
      ⊥
    invariantPreservedUnderTransform :
      Symbolic.symbolInvariant directCarrier
      ≡
      Symbolic.symbolInvariant transformedCarrier
    transformedCostNoGreater :
      transformedCarrierAccessCost ≤ directCarrierAccessCost
    priorAccessRegime :
      Unconscious.AccessAvoidanceRegime

open StableUnconsciousWitness public

canonicalStableUnconsciousWitness : StableUnconsciousWitness
canonicalStableUnconsciousWitness =
  stableUnconsciousWitness
    true
    stableBlockingAcrossPerturbations
    blockedCarrierStillInfluencesAction
    carrierInvariantPreserved
    transformedCarrierCostLower
    Unconscious.canonicalAccessAvoidanceRegime

record StableUnconsciousBoundary : Set where
  constructor stableUnconsciousBoundary
  field
    stabilityDiagnosesRepression : Bool
    stabilityDiagnosesRepressionIsFalse :
      stabilityDiagnosesRepression ≡ false

    accessLevelIsMeasuredClinicalThreshold : Bool
    accessLevelIsMeasuredClinicalThresholdIsFalse :
      accessLevelIsMeasuredClinicalThreshold ≡ false

open StableUnconsciousBoundary public

canonicalStableUnconsciousBoundary : StableUnconsciousBoundary
canonicalStableUnconsciousBoundary =
  stableUnconsciousBoundary false refl false refl
