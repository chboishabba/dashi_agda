module DASHI.Foundations.PMApparentVariableDescriptionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (Σ; _,_)

------------------------------------------------------------------------
-- Apparent-variable and description boundary.
--
-- Definite descriptions are represented as receipt-bearing sockets.  This
-- file intentionally does not make descriptions total terms.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

Predicate : Set → Set₁
Predicate A =
  A → Set

record ApparentVariable (A : Set) : Set₁ where
  constructor mkApparentVariable
  field
    variableLabel :
      String

    admissibleValues :
      Predicate A

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

Exists : ∀ {A : Set} → Predicate A → Set
Exists {A = A} P =
  Σ A P

Forall : ∀ {A : Set} → Predicate A → Set
Forall {A = A} P =
  (x : A) → P x

record SubstitutionReceipt (A : Set) : Set₁ where
  constructor mkSubstitutionReceipt
  field
    receiptLabel :
      String

    sourceVariable :
      ApparentVariable A

    targetVariable :
      ApparentVariable A

    admissibilityChecked :
      Bool

    admissibilityCheckedIsTrue :
      admissibilityChecked ≡ true

record DescriptionSocket (A : Set) : Set₁ where
  constructor mkDescriptionSocket
  field
    socketLabel :
      String

    definingPredicate :
      Predicate A

    substitutionReceipt :
      SubstitutionReceipt A

    totalTermAuthority :
      Bool

    totalTermAuthorityIsFalse :
      totalTermAuthority ≡ false

    incompleteSymbolBoundary :
      Bool

    incompleteSymbolBoundaryIsTrue :
      incompleteSymbolBoundary ≡ true

record DescriptionAuthorityBoundary : Set where
  constructor mkDescriptionAuthorityBoundary
  field
    boundaryLabel :
      String

    apparentVariableSocketPresent :
      Bool

    apparentVariableSocketPresentIsTrue :
      apparentVariableSocketPresent ≡ true

    descriptionTotalityAuthority :
      Bool

    descriptionTotalityAuthorityIsFalse :
      descriptionTotalityAuthority ≡ false

    pmSubstitutionCalculusAuthority :
      Bool

    pmSubstitutionCalculusAuthorityIsFalse :
      pmSubstitutionCalculusAuthority ≡ false

canonicalDescriptionAuthorityBoundary :
  DescriptionAuthorityBoundary
canonicalDescriptionAuthorityBoundary =
  mkDescriptionAuthorityBoundary
    "pm-apparent-variable-description-boundary"
    true
    refl
    false
    refl
    false
    refl

BoolTrueVariable : ApparentVariable Bool
BoolTrueVariable =
  mkApparentVariable
    "bool-true-apparent-variable"
    (λ b → b ≡ true)
    true
    refl

BoolTrueSubstitutionReceipt : SubstitutionReceipt Bool
BoolTrueSubstitutionReceipt =
  mkSubstitutionReceipt
    "bool-true-substitution-receipt"
    BoolTrueVariable
    BoolTrueVariable
    true
    refl

BoolTrueDescriptionSocket : DescriptionSocket Bool
BoolTrueDescriptionSocket =
  mkDescriptionSocket
    "bool-true-description-socket"
    (λ b → b ≡ true)
    BoolTrueSubstitutionReceipt
    false
    refl
    true
    refl

descriptionSocketDoesNotMakeTotalTerm :
  DescriptionSocket.totalTermAuthority BoolTrueDescriptionSocket ≡ false
descriptionSocketDoesNotMakeTotalTerm =
  refl
