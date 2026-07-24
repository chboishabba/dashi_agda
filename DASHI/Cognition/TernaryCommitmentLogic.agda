module DASHI.Cognition.TernaryCommitmentLogic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- Ternary commitment is not a refutation of classical excluded middle.
--
-- For a decidable finite claim, truth may already be true or false while the
-- cognitive/observational commitment gate remains projective.  The third value
-- belongs to evidence, admissibility, or binding status rather than adding a
-- third classical truth value by fiat.
------------------------------------------------------------------------

data FiniteClaim : Set where
  present absent : FiniteClaim

data IsPresent : FiniteClaim → Set where
  presentWitness : IsPresent present

data IsAbsent : FiniteClaim → Set where
  absentWitness : IsAbsent absent

finiteExcludedMiddle :
  (claim : FiniteClaim) → IsPresent claim ⊎ IsAbsent claim
finiteExcludedMiddle present = inj₁ presentWitness
finiteExcludedMiddle absent = inj₂ absentWitness

record CommitmentState : Set where
  constructor commitmentState
  field
    claim       : FiniteClaim
    publicTruth : Bool
    gate        : BT.Trit

open CommitmentState public

truthKnownCommitmentOpen : CommitmentState
truthKnownCommitmentOpen = commitmentState present true BT.zero

truthKnownCommitmentBound : CommitmentState
truthKnownCommitmentBound = commitmentState present true BT.pos

sameTruthDifferentCommitment :
  publicTruth truthKnownCommitmentOpen
  ≡ publicTruth truthKnownCommitmentBound
sameTruthDifferentCommitment = refl

projectiveGateCoexistsWithTrueClaim :
  gate truthKnownCommitmentOpen ≡ BT.zero
projectiveGateCoexistsWithTrueClaim = refl

record CommitmentPolicy : Set where
  constructor commitmentPolicy
  field
    unresolvedGate : BT.Trit
    acceptedGate   : BT.Trit
    rejectedGate   : BT.Trit

canonicalCommitmentPolicy : CommitmentPolicy
canonicalCommitmentPolicy = commitmentPolicy BT.zero BT.pos BT.neg

------------------------------------------------------------------------
-- The psychedelic conjecture is therefore a policy/dynamics claim: longer
-- residence at the unresolved gate, not abolition of the proposition-level
-- excluded-middle witness above.
------------------------------------------------------------------------

data LogicalAuthority : Set where
  excludedMiddleRetained
  ternaryCommitmentAdded
  threeValuedTruthNotForced : LogicalAuthority
