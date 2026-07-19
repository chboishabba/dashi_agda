module DASHI.Vision.Surfel.PromotionOrder where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- The runtime surface has three trust states.  This module deliberately
-- separates the state order from any particular floating-point score.

data SurfelState : Set where
  grounded plateau ascended : SurfelState

infix 4 _⊑_

data _⊑_ : SurfelState → SurfelState → Set where
  grounded-refl : grounded ⊑ grounded
  grounded-plateau : grounded ⊑ plateau
  grounded-ascended : grounded ⊑ ascended
  plateau-refl : plateau ⊑ plateau
  plateau-ascended : plateau ⊑ ascended
  ascended-refl : ascended ⊑ ascended

⊑-refl : (s : SurfelState) → s ⊑ s
⊑-refl grounded = grounded-refl
⊑-refl plateau = plateau-refl
⊑-refl ascended = ascended-refl

⊑-trans : {a b c : SurfelState} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans grounded-refl q = q
⊑-trans grounded-plateau plateau-refl = grounded-plateau
⊑-trans grounded-plateau plateau-ascended = grounded-ascended
⊑-trans grounded-ascended ascended-refl = grounded-ascended
⊑-trans plateau-refl q = q
⊑-trans plateau-ascended ascended-refl = plateau-ascended
⊑-trans ascended-refl ascended-refl = ascended-refl

------------------------------------------------------------------------
-- Evidence is intentionally integer-valued at this proof boundary.  Runtime
-- floats are quantised before entering the formal interface.

record SurfelEvidence : Set where
  constructor evidence
  field
    accumulatedWeight : Nat
    temporalHits : Nat
    neighbourSupport : Nat
    residual : Nat

open SurfelEvidence public

record PromotionThresholds : Set where
  constructor thresholds
  field
    plateauScore : Nat
    ascendedScore : Nat
    ascendedHits : Nat
    residualCeiling : Nat

open PromotionThresholds public

------------------------------------------------------------------------
-- A classifier may use any concrete score, but must return witnesses for the
-- guard it claims to have crossed.

record GuardedClassifier : Set₁ where
  field
    score : SurfelEvidence → Nat

    classify : SurfelEvidence → SurfelState

    groundedWitness :
      (e : SurfelEvidence) →
      classify e ≡ grounded →
      Set

    plateauWitness :
      (e : SurfelEvidence) →
      classify e ≡ plateau →
      Set

    ascendedWitness :
      (e : SurfelEvidence) →
      classify e ≡ ascended →
      Set

open GuardedClassifier public

------------------------------------------------------------------------
-- Quality ordering is a separate theorem obligation.  Count growth alone is
-- never accepted as evidence that ascended is cleaner than plateau.

record QualityOrderedPromotion
       (Residual : SurfelState → Nat)
       : Set where
  field
    ascendedCleanerThanPlateau : Set
    qualityWitness : ascendedCleanerThanPlateau

open QualityOrderedPromotion public

------------------------------------------------------------------------
-- Fail-closed boundary: an impossible promotion authority cannot be forged.

data UnguardedAscensionAuthority : Set where

noUnguardedAscension : UnguardedAscensionAuthority → ⊥
noUnguardedAscension ()
