module DASHI.Topology.FiniteBraidRhizomeCalculus where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Strand : Set where
  leftStrand rightStrand : Strand

data Braid2 : Set where
  straight swap : Braid2

compose : Braid2 → Braid2 → Braid2
compose straight b = b
compose swap straight = swap
compose swap swap = straight

inverse : Braid2 → Braid2
inverse straight = straight
inverse swap = swap

act : Braid2 → Strand → Strand
act straight s = s
act swap leftStrand = rightStrand
act swap rightStrand = leftStrand

composeIdentityLeft : (b : Braid2) → compose straight b ≡ b
composeIdentityLeft straight = refl
composeIdentityLeft swap = refl

composeIdentityRight : (b : Braid2) → compose b straight ≡ b
composeIdentityRight straight = refl
composeIdentityRight swap = refl

composeAssociative :
  (a b c : Braid2) →
  compose (compose a b) c ≡ compose a (compose b c)
composeAssociative straight straight straight = refl
composeAssociative straight straight swap = refl
composeAssociative straight swap straight = refl
composeAssociative straight swap swap = refl
composeAssociative swap straight straight = refl
composeAssociative swap straight swap = refl
composeAssociative swap swap straight = refl
composeAssociative swap swap swap = refl

inverseLeft : (b : Braid2) → compose (inverse b) b ≡ straight
inverseLeft straight = refl
inverseLeft swap = refl

inverseRight : (b : Braid2) → compose b (inverse b) ≡ straight
inverseRight straight = refl
inverseRight swap = refl

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

strandDistinct : leftStrand ≠ rightStrand
strandDistinct ()

collisionFree :
  (b : Braid2) →
  act b leftStrand ≠ act b rightStrand
collisionFree straight = strandDistinct
collisionFree swap ()

data IsotopyClass2 : Set where
  evenCrossing oddCrossing : IsotopyClass2

classify : Braid2 → IsotopyClass2
classify straight = evenCrossing
classify swap = oddCrossing

classificationComplete :
  (b : Braid2) →
  classify b ≡ evenCrossing ⊎ classify b ≡ oddCrossing
classificationComplete straight = inj₁ refl
classificationComplete swap = inj₂ refl

data FlexBudget : Set where
  rigid flexible : FlexBudget

data CanRealise : FlexBudget → Braid2 → Set where
  realiseStraightRigid : CanRealise rigid straight
  realiseStraightFlexible : CanRealise flexible straight
  realiseSwapFlexible : CanRealise flexible swap

data TranslationOutcome : Set where
  translatedExactly translationNeedsRefinement : TranslationOutcome

translateWithBudget : FlexBudget → Braid2 → TranslationOutcome
translateWithBudget rigid straight = translatedExactly
translateWithBudget rigid swap = translationNeedsRefinement
translateWithBudget flexible straight = translatedExactly
translateWithBudget flexible swap = translatedExactly

realisationImpliesTranslation :
  ∀ {budget braid} →
  CanRealise budget braid →
  translateWithBudget budget braid ≡ translatedExactly
realisationImpliesTranslation realiseStraightRigid = refl
realisationImpliesTranslation realiseStraightFlexible = refl
realisationImpliesTranslation realiseSwapFlexible = refl

data Tube : Set where
  trunk leftBranch rightBranch : Tube

data Junction : Set where
  splitJunction mergeJunction reconnectJunction : Junction

data SectionRoute : Junction → Tube → Tube → Set where
  splitLeft : SectionRoute splitJunction trunk leftBranch
  splitRight : SectionRoute splitJunction trunk rightBranch
  mergeLeft : SectionRoute mergeJunction leftBranch trunk
  mergeRight : SectionRoute mergeJunction rightBranch trunk
  reconnectLR : SectionRoute reconnectJunction leftBranch rightBranch
  reconnectRL : SectionRoute reconnectJunction rightBranch leftBranch

reverseJunction : Junction → Junction
reverseJunction splitJunction = mergeJunction
reverseJunction mergeJunction = splitJunction
reverseJunction reconnectJunction = reconnectJunction

reverseRoute :
  ∀ {j x y} →
  SectionRoute j x y →
  SectionRoute (reverseJunction j) y x
reverseRoute splitLeft = mergeLeft
reverseRoute splitRight = mergeRight
reverseRoute mergeLeft = splitLeft
reverseRoute mergeRight = splitRight
reverseRoute reconnectLR = reconnectRL
reverseRoute reconnectRL = reconnectLR

record FiniteBraidRhizomeReceipt : Set where
  constructor mkFiniteBraidRhizomeReceipt
  field
    braidIdentityChecked : Bool
    braidAssociativityChecked : Bool
    inversesChecked : Bool
    collisionAvoidanceChecked : Bool
    twoIsotopyClassesChecked : Bool
    flexibilityControlsSwapTranslation : Bool
    splitMergeRouteReversalChecked : Bool
    arbitraryBraidGroupPromoted : Bool
    arbitraryBraidGroupPromotedIsFalse : arbitraryBraidGroupPromoted ≡ false
    arbitraryRecursivePantsBundlePromoted : Bool
    arbitraryRecursivePantsBundlePromotedIsFalse :
      arbitraryRecursivePantsBundlePromoted ≡ false
    interpretation : String

finiteBraidRhizomeReceipt : FiniteBraidRhizomeReceipt
finiteBraidRhizomeReceipt =
  mkFiniteBraidRhizomeReceipt
    true true true true true true true
    false refl false refl
    "the exact two-strand parity braid, collision avoidance, flexibility-gated translation, and reversible split/merge routes are checked; higher braid groups, isotopy spaces and arbitrary recursively glued pants bundles remain explicit extensions"
