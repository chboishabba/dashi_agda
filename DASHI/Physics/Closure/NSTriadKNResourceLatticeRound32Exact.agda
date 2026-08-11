module DASHI.Physics.Closure.NSTriadKNResourceLatticeRound32Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Compile the admissible remainder grammar to a product-valued resource
-- ledger.  The fourth coordinate records forbidden continuation resources.
-- Because the source grammar has no constructor for BKM, Serrin, or the
-- target critical supremum, that coordinate is proved identically zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleRemainderGrammarRound31Exact as Grammar

record ResourceVector : Set where
  constructor resource-vector
  field
    dissipationCoordinate : ℚ
    dataCoordinate : ℚ
    criticalCoordinate : ℚ
    forbiddenCoordinate : ℚ

open ResourceVector public

_⊞_ : ResourceVector → ResourceVector → ResourceVector
left ⊞ right = resource-vector
  (dissipationCoordinate left + dissipationCoordinate right)
  (dataCoordinate left + dataCoordinate right)
  (criticalCoordinate left + criticalCoordinate right)
  (forbiddenCoordinate left + forbiddenCoordinate right)

infixr 5 _⊞_

remainderValuation : Grammar.AdmissibleRemainder → ResourceVector
remainderValuation (Grammar.initialDataConstant coefficient) =
  resource-vector 0ℚ coefficient 0ℚ 0ℚ
remainderValuation (Grammar.knownCriticalIntegral coefficient) =
  resource-vector 0ℚ 0ℚ coefficient 0ℚ
remainderValuation (Grammar.lowerOrderControlled coefficient) =
  resource-vector 0ℚ coefficient 0ℚ 0ℚ
remainderValuation (Grammar.absorbedDissipation coefficient) =
  resource-vector coefficient 0ℚ 0ℚ 0ℚ
remainderValuation (Grammar._⊕_ left right) =
  remainderValuation left ⊞ remainderValuation right

valuationEtaExact :
  ∀ remainder →
  dissipationCoordinate (remainderValuation remainder)
  ≡ Grammar.remainderEta remainder
valuationEtaExact (Grammar.initialDataConstant coefficient) = refl
valuationEtaExact (Grammar.knownCriticalIntegral coefficient) = refl
valuationEtaExact (Grammar.lowerOrderControlled coefficient) = refl
valuationEtaExact (Grammar.absorbedDissipation coefficient) = refl
valuationEtaExact (Grammar._⊕_ left right) =
  cong₂ _+_ (valuationEtaExact left) (valuationEtaExact right)

valuationCriticalExact :
  ∀ remainder →
  criticalCoordinate (remainderValuation remainder)
  ≡ Grammar.remainderCriticalCoefficient remainder
valuationCriticalExact (Grammar.initialDataConstant coefficient) = refl
valuationCriticalExact (Grammar.knownCriticalIntegral coefficient) = refl
valuationCriticalExact (Grammar.lowerOrderControlled coefficient) = refl
valuationCriticalExact (Grammar.absorbedDissipation coefficient) = refl
valuationCriticalExact (Grammar._⊕_ left right) =
  cong₂ _+_ (valuationCriticalExact left) (valuationCriticalExact right)

noForbiddenValuation :
  ∀ remainder →
  forbiddenCoordinate (remainderValuation remainder) ≡ 0ℚ
noForbiddenValuation (Grammar.initialDataConstant coefficient) = refl
noForbiddenValuation (Grammar.knownCriticalIntegral coefficient) = refl
noForbiddenValuation (Grammar.lowerOrderControlled coefficient) = refl
noForbiddenValuation (Grammar.absorbedDissipation coefficient) = refl
noForbiddenValuation (Grammar._⊕_ left right) =
  trans
    (cong₂ _+_
      (noForbiddenValuation left)
      (noForbiddenValuation right))
    (solve ([]))

data OwnerDerivation :
    Grammar.AdmissibleRemainder →
    Grammar.AdmissibleRemainder → Set where
  identity : ∀ {remainder} → OwnerDerivation remainder remainder
  appendInitial : ∀ {remainder coefficient} →
    OwnerDerivation remainder
      (Grammar._⊕_ remainder (Grammar.initialDataConstant coefficient))
  appendCritical : ∀ {remainder coefficient} →
    OwnerDerivation remainder
      (Grammar._⊕_ remainder (Grammar.knownCriticalIntegral coefficient))
  appendLowerOrder : ∀ {remainder coefficient} →
    OwnerDerivation remainder
      (Grammar._⊕_ remainder (Grammar.lowerOrderControlled coefficient))
  appendDissipation : ∀ {remainder coefficient} →
    OwnerDerivation remainder
      (Grammar._⊕_ remainder (Grammar.absorbedDissipation coefficient))
  compose : ∀ {first middle last} →
    OwnerDerivation first middle →
    OwnerDerivation middle last →
    OwnerDerivation first last

ownerDerivationCannotCreateForbiddenCoordinate :
  ∀ {start finish} → OwnerDerivation start finish →
  forbiddenCoordinate (remainderValuation finish) ≡ 0ℚ
ownerDerivationCannotCreateForbiddenCoordinate {finish = finish} derivation =
  noForbiddenValuation finish

resourceLatticeClosed : Bool
resourceLatticeClosed = true

forbiddenResourceFailClosed : Bool
forbiddenResourceFailClosed = true

resourceLatticeClosedIsTrue : resourceLatticeClosed ≡ true
resourceLatticeClosedIsTrue = refl

forbiddenResourceFailClosedIsTrue :
  forbiddenResourceFailClosed ≡ true
forbiddenResourceFailClosedIsTrue = refl
