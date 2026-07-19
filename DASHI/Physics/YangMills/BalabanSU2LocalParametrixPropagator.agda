module DASHI.Physics.YangMills.BalabanSU2LocalParametrixPropagator where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

infixr 9 _∘_
infix 4 _≈_
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

_≈_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → Set (a ⊔ b)
f ≈ g = ∀ x → f x ≡ g x

LeftInverse : ∀ {a} {A : Set a} → (A → A) → (A → A) → Set a
LeftInverse operator inverse = inverse ∘ operator ≈ id

RightInverse : ∀ {a} {A : Set a} → (A → A) → (A → A) → Set a
RightInverse operator inverse = operator ∘ inverse ≈ id

record TwoSidedInverse {a : Level} (A : Set a) (operator : A → A) : Set a where
  constructor twoSidedInverse
  field
    inverse : A → A
    inverseLeft : LeftInverse operator inverse
    inverseRight : RightInverse operator inverse
open TwoSidedInverse public

parametrixRightInverse :
  ∀ {a} {A : Set a}
  (operator local residual residualInverse : A → A) →
  (∀ x → operator (local x) ≡ residual x) →
  RightInverse residual residualInverse →
  RightInverse operator (local ∘ residualInverse)
parametrixRightInverse operator local residual residualInverse equation law x =
  trans (equation (residualInverse x)) (law x)

parametrixLeftInverse :
  ∀ {a} {A : Set a}
  (operator local residual residualInverse : A → A) →
  (∀ x → local (operator x) ≡ residual x) →
  LeftInverse residual residualInverse →
  LeftInverse operator (residualInverse ∘ local)
parametrixLeftInverse operator local residual residualInverse equation law x =
  trans (cong residualInverse (equation x)) (law x)

leftRightInverseUnique :
  ∀ {a} {A : Set a}
  (operator left right : A → A) →
  LeftInverse operator left →
  RightInverse operator right →
  left ≈ right
leftRightInverseUnique operator left right leftLaw rightLaw x =
  trans (sym (cong left (rightLaw x))) (leftLaw (right x))

propagatorTwoSidedInverse :
  ∀ {a} {A : Set a}
  (operator local : A → A)
  (rightResidual rightResidualInverse : A → A)
  (leftResidual leftResidualInverse : A → A) →
  (∀ x → operator (local x) ≡ rightResidual x) →
  RightInverse rightResidual rightResidualInverse →
  (∀ x → local (operator x) ≡ leftResidual x) →
  LeftInverse leftResidual leftResidualInverse →
  TwoSidedInverse A operator
propagatorTwoSidedInverse
  operator local rightResidual rightResidualInverse
  leftResidual leftResidualInverse
  rightEquation rightLaw leftEquation leftLaw =
  twoSidedInverse rightCandidate rightCandidateLeft rightCandidateRight
  where
    rightCandidate : _
    rightCandidate = local ∘ rightResidualInverse

    leftCandidate : _
    leftCandidate = leftResidualInverse ∘ local

    rightCandidateRight : RightInverse operator rightCandidate
    rightCandidateRight =
      parametrixRightInverse
        operator local rightResidual rightResidualInverse rightEquation rightLaw

    leftCandidateLeft : LeftInverse operator leftCandidate
    leftCandidateLeft =
      parametrixLeftInverse
        operator local leftResidual leftResidualInverse leftEquation leftLaw

    candidatesEqual : leftCandidate ≈ rightCandidate
    candidatesEqual =
      leftRightInverseUnique
        operator leftCandidate rightCandidate leftCandidateLeft rightCandidateRight

    rightCandidateLeft : LeftInverse operator rightCandidate
    rightCandidateLeft x =
      trans (sym (candidatesEqual (operator x))) (leftCandidateLeft x)
