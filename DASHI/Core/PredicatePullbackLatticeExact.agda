module DASHI.Core.PredicatePullbackLatticeExact where

open import DASHI.Core.Prelude
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

Predicate : Set → Set
Predicate A = A → Bool

andB : Bool → Bool → Bool
andB true true = true
andB _ _ = false

orB : Bool → Bool → Bool
orB false false = false
orB _ _ = true

infixr 6 _⊓p_
infixr 5 _⊔p_

_⊓p_ : ∀ {A : Set} → Predicate A → Predicate A → Predicate A
(p ⊓p q) x = andB (p x) (q x)

_⊔p_ : ∀ {A : Set} → Predicate A → Predicate A → Predicate A
(p ⊔p q) x = orB (p x) (q x)

pullbackPredicate : ∀ {Fine Coarse : Set} → (Fine → Coarse) → Predicate Coarse → Predicate Fine
pullbackPredicate project predicate fine = predicate (project fine)

FibreConstantPredicate : ∀ {Fine Coarse : Set} → (Fine → Coarse) → Predicate Fine → Set
FibreConstantPredicate project predicate = ∀ x y → project x ≡ project y → predicate x ≡ predicate y

pulledBackPredicateIsFibreConstant : ∀ {Fine Coarse : Set} (project : Fine → Coarse) (predicate : Predicate Coarse) → FibreConstantPredicate project (pullbackPredicate project predicate)
pulledBackPredicateIsFibreConstant project predicate x y equality = cong predicate equality

pullbackPreservesMeet : ∀ {Fine Coarse : Set} (project : Fine → Coarse) (p q : Predicate Coarse) (x : Fine) → pullbackPredicate project (p ⊓p q) x ≡ (pullbackPredicate project p ⊓p pullbackPredicate project q) x
pullbackPreservesMeet project p q x = refl

pullbackPreservesJoin : ∀ {Fine Coarse : Set} (project : Fine → Coarse) (p q : Predicate Coarse) (x : Fine) → pullbackPredicate project (p ⊔p q) x ≡ (pullbackPredicate project p ⊔p pullbackPredicate project q) x
pullbackPreservesJoin project p q x = refl

representativePredicate : ∀ {Fine Coarse : Set} → Sectioned.SectionedProjection Fine Coarse → Predicate Fine → Predicate Coarse
representativePredicate projection predicate coarse = predicate (Sectioned.representative projection coarse)

fibreConstantPredicateReconstructsFromSection : ∀ {Fine Coarse : Set} (projection : Sectioned.SectionedProjection Fine Coarse) (predicate : Predicate Fine) → FibreConstantPredicate (Sectioned.project projection) predicate → (x : Fine) → predicate x ≡ pullbackPredicate (Sectioned.project projection) (representativePredicate projection predicate) x
fibreConstantPredicateReconstructsFromSection projection predicate constant x = constant x (Sectioned.representative projection (Sectioned.project projection x)) (sym (Sectioned.section projection (Sectioned.project projection x)))

record PredicatePullbackLatticeBoundary : Set where
  constructor predicatePullbackLatticeBoundary
  field
    coarsePredicatesPullBackFibreConstant : Bool
    coarsePredicatesPullBackFibreConstantIsTrue : coarsePredicatesPullBackFibreConstant ≡ true
    pullbackPreservesPredicateMeet : Bool
    pullbackPreservesPredicateMeetIsTrue : pullbackPreservesPredicateMeet ≡ true
    pullbackPreservesPredicateJoin : Bool
    pullbackPreservesPredicateJoinIsTrue : pullbackPreservesPredicateJoin ≡ true
    sectionReconstructsFibreConstantFinePredicates : Bool
    sectionReconstructsFibreConstantFinePredicatesIsTrue : sectionReconstructsFibreConstantFinePredicates ≡ true

canonicalPredicatePullbackLatticeBoundary : PredicatePullbackLatticeBoundary
canonicalPredicatePullbackLatticeBoundary = predicatePullbackLatticeBoundary true refl true refl true refl true refl
