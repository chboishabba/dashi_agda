module DASHI.Analysis.MarxFieldCancellation where

open import Agda.Primitive using (Set; Set₁)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxReciprocalQuotientNormalisation

private
  _≢_ : {X : Set} → X → X → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Connect the selected field's Nonzero predicate to ordinary apartness.

record NonzeroApartnessCompatibility
  {A : MarxAlgebra}
  (L : MarxReciprocalLaws A)
  : Set₁ where
  field
    nonzeroImpliesApart :
      ∀ {x} → Nonzero L x → x ≢ zero A

    apartImpliesNonzero :
      ∀ {x} → x ≢ zero A → Nonzero L x

open NonzeroApartnessCompatibility public

------------------------------------------------------------------------
-- Cancellation laws for nonzero factors.

record MarxCancellationLaws
  {A : MarxAlgebra}
  (L : MarxReciprocalLaws A)
  : Set₁ where
  field
    mulCancelLeftNonzero :
      ∀ x {a b} →
      Nonzero L x →
      _*_ A x a ≡ _*_ A x b →
      a ≡ b

    mulCancelRightNonzero :
      ∀ x {a b} →
      Nonzero L x →
      _*_ A a x ≡ _*_ A b x →
      a ≡ b

open MarxCancellationLaws public

------------------------------------------------------------------------
-- Reciprocal uniqueness is derived from right cancellation.

reciprocalUnique :
  {A : MarxAlgebra} →
  {L : MarxReciprocalLaws A} →
  MarxCancellationLaws L →
  ∀ x →
  Nonzero L x →
  ∀ candidate →
  _*_ A candidate x ≡ one A →
  candidate ≡ reciprocal L x
reciprocalUnique {A} {L} cancellation x nonzeroX candidate candidateInverse =
  mulCancelRightNonzero cancellation x nonzeroX
    (trans
      candidateInverse
      (sym (mulReciprocalLeft L x nonzeroX)))

reciprocalUniqueFromRightInverse :
  {A : MarxAlgebra} →
  {L : MarxReciprocalLaws A} →
  MarxCancellationLaws L →
  ∀ x →
  Nonzero L x →
  ∀ candidate →
  _*_ A x candidate ≡ one A →
  candidate ≡ reciprocal L x
reciprocalUniqueFromRightInverse {A} {L} cancellation x nonzeroX candidate candidateInverse =
  mulCancelLeftNonzero cancellation x nonzeroX
    (trans
      candidateInverse
      (sym (mulReciprocalRight L x nonzeroX)))

------------------------------------------------------------------------
-- A compact field completion packet for the reciprocal/quotient lane.

record MarxFieldCompletion
  (A : MarxAlgebra)
  : Set₁ where
  field
    reciprocalLaws : MarxReciprocalLaws A
    nonzeroApartness : NonzeroApartnessCompatibility reciprocalLaws
    cancellationLaws : MarxCancellationLaws reciprocalLaws
    quotientNormalisation :
      QuotientDenominatorSquareNormalisation reciprocalLaws

open MarxFieldCompletion public
