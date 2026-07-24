module DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier

------------------------------------------------------------------------
-- Duplicate-free finite list calculus for the repository's literal
-- enumeration and Cartesian-product definitions.
------------------------------------------------------------------------

_∉_ : ∀ {A : Set} → A → List A → Set
value ∉ values = value ∈ values → ⊥

data DuplicateFree {A : Set} : List A → Set where
  []-free : DuplicateFree []
  _∷-free_ : ∀ {value values} →
    value ∉ values → DuplicateFree values →
    DuplicateFree (value ∷ values)

infixr 5 _∷-free_

zeroNotInSucMap : ∀ {n} →
  zeroᵢ ∉ map sucᵢ (allCyclicIndices n)
zeroNotInSucMap ()

sucMapMembershipInverse :
  ∀ {n} {left : CyclicIndex n} {values} →
  sucᵢ left ∈ map sucᵢ values →
  left ∈ values
sucMapMembershipInverse {values = value ∷ values} here = here
sucMapMembershipInverse {values = value ∷ values} (there membership) =
  there (sucMapMembershipInverse membership)

sucMapNotMember :
  ∀ {n} {value : CyclicIndex n} {values} →
  value ∉ values →
  sucᵢ value ∉ map sucᵢ values
sucMapNotMember notMember membership =
  notMember (sucMapMembershipInverse membership)

sucMapDuplicateFree :
  ∀ {n} {values : List (CyclicIndex n)} →
  DuplicateFree values →
  DuplicateFree (map sucᵢ values)
sucMapDuplicateFree []-free = []-free
sucMapDuplicateFree (notMember ∷-free restFree) =
  sucMapNotMember notMember ∷-free sucMapDuplicateFree restFree

allCyclicIndicesDuplicateFree : ∀ n →
  DuplicateFree (allCyclicIndices n)
allCyclicIndicesDuplicateFree zero = []-free
allCyclicIndicesDuplicateFree (suc n) =
  zeroNotInSucMap ∷-free
    sucMapDuplicateFree (allCyclicIndicesDuplicateFree n)

------------------------------------------------------------------------
-- Generic append and injective-map preservation.
------------------------------------------------------------------------

mapMembershipInverse :
  ∀ {A B : Set} {f : A → B} {target values} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  f target ∈ map f values →
  target ∈ values
mapMembershipInverse injective {values = value ∷ values} here =
  subst (λ candidate → candidate ∈ value ∷ values)
    (sym (injective refl)) here
mapMembershipInverse injective {values = value ∷ values} (there membership) =
  there (mapMembershipInverse injective membership)

mapNotMember :
  ∀ {A B : Set} {f : A → B} {target values} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  target ∉ values →
  f target ∉ map f values
mapNotMember injective notMember membership =
  notMember (mapMembershipInverse injective membership)

mapDuplicateFree :
  ∀ {A B : Set} {f : A → B} {values} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  DuplicateFree values →
  DuplicateFree (map f values)
mapDuplicateFree injective []-free = []-free
mapDuplicateFree injective (notMember ∷-free restFree) =
  mapNotMember injective notMember ∷-free
    mapDuplicateFree injective restFree

splitAppendMembership :
  ∀ {A : Set} {value : A} {left right} →
  value ∈ (left ++ right) →
  (value ∈ left) ⊎ (value ∈ right)
splitAppendMembership {left = []} membership = inj₂ membership
splitAppendMembership {left = item ∷ left} here = inj₁ here
splitAppendMembership {left = item ∷ left} (there membership)
  with splitAppendMembership membership
... | inj₁ inLeft = inj₁ (there inLeft)
... | inj₂ inRight = inj₂ inRight

notInAppend :
  ∀ {A : Set} {value : A} {left right} →
  value ∉ left → value ∉ right →
  value ∉ (left ++ right)
notInAppend notLeft notRight membership
  with splitAppendMembership membership
... | inj₁ inLeft = notLeft inLeft
... | inj₂ inRight = notRight inRight

record Disjoint {A : Set} (left right : List A) : Set where
  field
    disjoint : ∀ {value} → value ∈ left → value ∈ right → ⊥

open Disjoint public

appendDuplicateFree :
  ∀ {A : Set} {left right : List A} →
  DuplicateFree left → DuplicateFree right →
  Disjoint left right →
  DuplicateFree (left ++ right)
appendDuplicateFree []-free rightFree separated = rightFree
appendDuplicateFree
  (notTail ∷-free tailFree) rightFree separated =
  notInAppend notTail
      (λ inRight → disjoint separated here inRight)
  ∷-free
  appendDuplicateFree tailFree rightFree record
    { disjoint = λ inTail inRight →
        disjoint separated (there inTail) inRight
    }

------------------------------------------------------------------------
-- Cartesian products preserve duplicate freeness.
------------------------------------------------------------------------

pairFixedInjective :
  ∀ {A B : Set} {fixed : A} {left right : B} →
  pair fixed left ≡ pair fixed right → left ≡ right
pairFixedInjective refl = refl

firstOf : ∀ {A B : Set} → Product A B → A
firstOf (pair first second) = first

firstOfMappedFixed :
  ∀ {A B : Set} {fixed : A} {value : Product A B} {values : List B} →
  value ∈ map (λ item → pair fixed item) values →
  firstOf value ≡ fixed
firstOfMappedFixed {values = item ∷ values} here = refl
firstOfMappedFixed {values = item ∷ values} (there membership) =
  firstOfMappedFixed membership

firstOfCartesianMembership :
  ∀ {A B : Set} {value : Product A B} {left : List A} {right : List B} →
  value ∈ cartesian left right →
  firstOf value ∈ left
firstOfCartesianMembership {left = []} ()
firstOfCartesianMembership {value = value} {left = item ∷ left} membership
  with splitAppendMembership membership
... | inj₁ inMapped =
  subst (λ candidate → candidate ∈ item ∷ left)
    (sym (firstOfMappedFixed inMapped)) here
... | inj₂ inRest = there (firstOfCartesianMembership inRest)

fixedBlockDisjointFromCartesianTail :
  ∀ {A B : Set} {fixed : A} {left : List A} {right : List B} →
  fixed ∉ left →
  Disjoint
    (map (λ item → pair fixed item) right)
    (cartesian left right)
fixedBlockDisjointFromCartesianTail {left = left} notInTail = record
  { disjoint = λ inFixed inTail →
      notInTail
        (subst
          (λ candidate → candidate ∈ left)
          (firstOfMappedFixed inFixed)
          (firstOfCartesianMembership inTail))
  }

cartesianDuplicateFree :
  ∀ {A B : Set} {left : List A} {right : List B} →
  DuplicateFree left → DuplicateFree right →
  DuplicateFree (cartesian left right)
cartesianDuplicateFree []-free rightFree = []-free
cartesianDuplicateFree
  (notInTail ∷-free tailFree) rightFree =
  appendDuplicateFree
    (mapDuplicateFree pairFixedInjective rightFree)
    (cartesianDuplicateFree tailFree rightFree)
    (fixedBlockDisjointFromCartesianTail notInTail)

cyclicEnumerationDuplicateFreeLevel : ProofLevel
cyclicEnumerationDuplicateFreeLevel = machineChecked

injectiveMapDuplicateFreeLevel : ProofLevel
injectiveMapDuplicateFreeLevel = machineChecked

cartesianEnumerationDuplicateFreeLevel : ProofLevel
cartesianEnumerationDuplicateFreeLevel = machineChecked
