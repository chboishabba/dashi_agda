module DASHI.Foundations.CantorDiagonalCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Constructive Cantor diagonalisation over type-theoretic predicates.
--
-- The result proved here is exactly non-surjectivity of A -> Pred A up to
-- pointwise logical equivalence.  It does not assert that arbitrary iteration,
-- residual production, social contradiction or psychic surplus raises
-- cardinality.  Those are separate bridge obligations.
------------------------------------------------------------------------

Pred : Set → Set₁
Pred A = A → Set

Not₁ : Set₁ → Set₁
Not₁ A = A → ⊥

infix 4 _≈ₚ_

_≈ₚ_ : ∀ {A} → Pred A → Pred A → Set
P ≈ₚ Q = ∀ x → (P x → Q x) × (Q x → P x)

predRefl : ∀ {A} (P : Pred A) → P ≈ₚ P
predRefl P x = (λ witness → witness) , (λ witness → witness)

predSym : ∀ {A} {P Q : Pred A} → P ≈ₚ Q → Q ≈ₚ P
predSym equivalence x = snd (equivalence x) , fst (equivalence x)

predTrans :
  ∀ {A} {P Q R : Pred A} →
  P ≈ₚ Q →
  Q ≈ₚ R →
  P ≈ₚ R
predTrans first second x =
  (λ witness → fst (second x) (fst (first x) witness)) ,
  (λ witness → snd (first x) (snd (second x) witness))

Diagonal : ∀ {A} → (A → Pred A) → Pred A
Diagonal enumeration x = ¬ enumeration x x

NotInImage : ∀ {A} → (A → Pred A) → Pred A → Set
NotInImage enumeration predicate =
  ∀ index → ¬ (enumeration index ≈ₚ predicate)

SurjectiveUpToPredicateEquivalence :
  ∀ {A} → (A → Pred A) → Set₁
SurjectiveUpToPredicateEquivalence enumeration =
  ∀ predicate → Σ A λ index → enumeration index ≈ₚ predicate

selfNegatingEquivalenceImpossible :
  ∀ {P : Set} →
  (P → ¬ P) →
  (¬ P → P) →
  ⊥
selfNegatingEquivalenceImpossible forward backward =
  notP p
  where
  notP : ¬ P
  notP witness = forward witness witness

  p : P
  p = backward notP

diagonalNotInImage :
  ∀ {A} (enumeration : A → Pred A) →
  NotInImage enumeration (Diagonal enumeration)
diagonalNotInImage enumeration index equivalence =
  selfNegatingEquivalenceImpossible
    (fst (equivalence index))
    (snd (equivalence index))

cantorNotSurjective :
  ∀ {A} (enumeration : A → Pred A) →
  Not₁ (SurjectiveUpToPredicateEquivalence enumeration)
cantorNotSurjective enumeration surjective =
  diagonalNotInImage enumeration
    (fst diagonalPreimage)
    (snd diagonalPreimage)
  where
  diagonalPreimage :
    Σ A λ index → enumeration index ≈ₚ Diagonal enumeration
  diagonalPreimage = surjective (Diagonal enumeration)

record CantorDiagonalReceipt (A : Set) : Set₁ where
  field
    enumeration : A → Pred A
    omittedPredicate : Pred A
    omittedPredicateIsDiagonal :
      omittedPredicate ≈ₚ Diagonal enumeration
    omittedFromImage :
      NotInImage enumeration omittedPredicate

canonicalCantorDiagonalReceipt :
  ∀ {A} (enumeration : A → Pred A) →
  CantorDiagonalReceipt A
canonicalCantorDiagonalReceipt enumeration = record
  { enumeration = enumeration
  ; omittedPredicate = Diagonal enumeration
  ; omittedPredicateIsDiagonal = predRefl (Diagonal enumeration)
  ; omittedFromImage = diagonalNotInImage enumeration
  }

record CantorAuthorityBoundary : Set where
  field
    selfIndexedPredicateTotalisationRefuted : Bool
    constructiveProofAvailable : Bool
    excludedMiddleRequired : Bool
    arbitraryResidualRaisesCardinalityClaimed : Bool
    countableIterationConstructsUncountableCarrierClaimed : Bool
    socialOrPsychologicalInterpretationPromoted : Bool
    sourceNote : String

canonicalCantorAuthorityBoundary : CantorAuthorityBoundary
canonicalCantorAuthorityBoundary = record
  { selfIndexedPredicateTotalisationRefuted = true
  ; constructiveProofAvailable = true
  ; excludedMiddleRequired = false
  ; arbitraryResidualRaisesCardinalityClaimed = false
  ; countableIterationConstructsUncountableCarrierClaimed = false
  ; socialOrPsychologicalInterpretationPromoted = false
  ; sourceNote =
      "Cantor's diagonal argument is implemented as predicate non-surjectivity; interpretive uses require separate governed bridges."
  }
