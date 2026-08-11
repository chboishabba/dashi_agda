module DASHI.Foundations.Base369CompletedRelationalDigitExact where

------------------------------------------------------------------------
-- A nonary address, balanced relational sign, completion state and scale are
-- independent coordinates.  In particular, residue zero can represent either
-- an empty/uninstantiated zero or a completed nine which emits a coarse carry.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

open import Base369 using
  ( NonaryTruth
  ; non-0
  )

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )

data CompletionBit : Set where
  uninstantiated
  instantiated : CompletionBit

data RelationalZeroWitness : Set where
  emptyZero
  balancedEvaluationZero
  invariantNeutralZero : RelationalZeroWitness

record RelationalDigit9 : Set where
  constructor relationalDigit9
  field
    address : NonaryTruth
    polarity : SSPTrit

open RelationalDigit9 public

record CompletedRelationalDigit9 : Set where
  constructor completedRelationalDigit9
  field
    digit : RelationalDigit9
    completion : CompletionBit

open CompletedRelationalDigit9 public

record NestedRelationalCell : Set where
  constructor nestedRelationalCell
  field
    cellAddress : NonaryTruth
    cellPolarity : SSPTrit
    cellCompletion : CompletionBit
    cellScale : Nat

open NestedRelationalCell public

emptyZeroDigit : CompletedRelationalDigit9
emptyZeroDigit =
  completedRelationalDigit9
    (relationalDigit9 non-0 sspZero)
    uninstantiated

completedNineDigit : CompletedRelationalDigit9
completedNineDigit =
  completedRelationalDigit9
    (relationalDigit9 non-0 sspZero)
    instantiated

emptyZeroIsUninstantiated :
  completion emptyZeroDigit ≡ uninstantiated
emptyZeroIsUninstantiated = refl

completedNineIsInstantiated :
  completion completedNineDigit ≡ instantiated
completedNineIsInstantiated = refl

emptyZeroCell : Nat → NestedRelationalCell
emptyZeroCell level =
  nestedRelationalCell non-0 sspZero uninstantiated level

completedNineCell : Nat → NestedRelationalCell
completedNineCell level =
  nestedRelationalCell non-0 sspZero instantiated level

-- Completion at residue zero is promoted to an uninstantiated zero at the next
-- containing scale.  The lower cell remains available as provenance; this map
-- describes only the emitted coarse state.
overflowCompletedNine : Nat → NestedRelationalCell
overflowCompletedNine level =
  nestedRelationalCell non-0 sspZero uninstantiated (suc level)

overflowPreservesZeroAddress :
  (level : Nat) →
  cellAddress (overflowCompletedNine level) ≡ non-0
overflowPreservesZeroAddress level = refl

overflowAdvancesScale :
  (level : Nat) →
  cellScale (overflowCompletedNine level) ≡ suc level
overflowAdvancesScale level = refl

------------------------------------------------------------------------
-- A dependent status carrier prevents the full raw product from being treated
-- as automatically meaningful.
------------------------------------------------------------------------

data DigitStatus : NonaryTruth → Set where
  emptyAtZero : DigitStatus non-0
  completedAtZero : DigitStatus non-0
  proposedAt : (digit : NonaryTruth) → DigitStatus digit
  realisedNegativeAt : (digit : NonaryTruth) → DigitStatus digit
  realisedNeutralAt : (digit : NonaryTruth) → DigitStatus digit
  realisedPositiveAt : (digit : NonaryTruth) → DigitStatus digit

record AdmissibleRelationalDigit : Set where
  constructor admissibleRelationalDigit
  field
    locatedAt : NonaryTruth
    status : DigitStatus locatedAt
    observedPolarity : SSPTrit

open AdmissibleRelationalDigit public

negativeProposalAt : NonaryTruth → AdmissibleRelationalDigit
negativeProposalAt digit =
  admissibleRelationalDigit digit (proposedAt digit) sspNegOne

neutralProposalAt : NonaryTruth → AdmissibleRelationalDigit
neutralProposalAt digit =
  admissibleRelationalDigit digit (proposedAt digit) sspZero

positiveProposalAt : NonaryTruth → AdmissibleRelationalDigit
positiveProposalAt digit =
  admissibleRelationalDigit digit (proposedAt digit) sspPosOne

completedNeutralIdentity : AdmissibleRelationalDigit
completedNeutralIdentity =
  admissibleRelationalDigit non-0 completedAtZero sspZero
