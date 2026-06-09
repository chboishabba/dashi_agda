module DASHI.Physics.Closure.NSA9CKNBKMClosureBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A9 CKN/BKM closure boundary.
--
-- This is a lightweight, fail-closed receipt for the claimed A9 closure
-- handoff only:
--
--   A9.1 iterate the A8 recursion so D_{theta^k r}(T*) -> 0;
--   A9.2 local enstrophy vanishing forces local vorticity vanishing;
--   A9.3 local omega = 0 implies local harmonic velocity by Biot-Savart;
--   A9.4 elliptic regularity / CKN exclusion contradicts singularity.
--
-- It records the standard closure route but proves no A9 theorem, no
-- Navier-Stokes Clay result, and no terminal promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Upstream references kept lightweight.

a8BoundaryReference : String
a8BoundaryReference =
  "DASHI.Physics.Closure.NSA8FullLocalDefectMonotonicityBoundary"

a8BoundaryConsumedRecorded : Bool
a8BoundaryConsumedRecorded =
  true

------------------------------------------------------------------------
-- A9 clauses.

data A9ClosureClause : Set where
  iterateA8ScaleRecursionToSmallerScales :
    A9ClosureClause
  localDefectSequenceConvergesToZeroAtSingularScale :
    A9ClosureClause
  vanishingLocalEnstrophyForcesLocalVorticityZero :
    A9ClosureClause
  biotSavartTurnsZeroVorticityIntoLocalHarmonicVelocity :
    A9ClosureClause
  ellipticRegularityRestoresSmoothness :
    A9ClosureClause
  cknBkmContradictionClosesNoSingularity :
    A9ClosureClause

canonicalA9ClosureClauses :
  List A9ClosureClause
canonicalA9ClosureClauses =
  iterateA8ScaleRecursionToSmallerScales
  ∷ localDefectSequenceConvergesToZeroAtSingularScale
  ∷ vanishingLocalEnstrophyForcesLocalVorticityZero
  ∷ biotSavartTurnsZeroVorticityIntoLocalHarmonicVelocity
  ∷ ellipticRegularityRestoresSmoothness
  ∷ cknBkmContradictionClosesNoSingularity
  ∷ []

a9ClosureClauseCount : Nat
a9ClosureClauseCount =
  listLength canonicalA9ClosureClauses

a9ClosureClauseCountIs6 :
  a9ClosureClauseCount ≡ 6
a9ClosureClauseCountIs6 =
  refl

data A9ClassicalInput : Set where
  input-a8ScaleMonotonicity :
    A9ClassicalInput
  input-cknSmallScaleCriterion :
    A9ClassicalInput
  input-bkmOrEquivalentLocalContinuationLanguage :
    A9ClassicalInput
  input-biotSavartLocalRegularityUpgrade :
    A9ClassicalInput

canonicalA9ClassicalInputs :
  List A9ClassicalInput
canonicalA9ClassicalInputs =
  input-a8ScaleMonotonicity
  ∷ input-cknSmallScaleCriterion
  ∷ input-bkmOrEquivalentLocalContinuationLanguage
  ∷ input-biotSavartLocalRegularityUpgrade
  ∷ []

a9ClassicalInputCount : Nat
a9ClassicalInputCount =
  listLength canonicalA9ClassicalInputs

a9ClassicalInputCountIs4 :
  a9ClassicalInputCount ≡ 4
a9ClassicalInputCountIs4 =
  refl

data DownstreamA9Blocker : Set where
  blocker-a9-closure-theorem-unproved :
    DownstreamA9Blocker
  blocker-ns-clay-authority-unproved :
    DownstreamA9Blocker
  blocker-terminal-promotion-forbidden :
    DownstreamA9Blocker

canonicalDownstreamA9Blockers :
  List DownstreamA9Blocker
canonicalDownstreamA9Blockers =
  blocker-a9-closure-theorem-unproved
  ∷ blocker-ns-clay-authority-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

downstreamA9BlockerCount : Nat
downstreamA9BlockerCount =
  listLength canonicalDownstreamA9Blockers

downstreamA9BlockerCountIs3 :
  downstreamA9BlockerCount ≡ 3
downstreamA9BlockerCountIs3 =
  refl

A9CKNBKMClosureProved : Bool
A9CKNBKMClosureProved =
  false

A9CKNBKMClosureProvedIsFalse :
  A9CKNBKMClosureProved ≡ false
A9CKNBKMClosureProvedIsFalse =
  refl

NSClayPromotedFromA9 : Bool
NSClayPromotedFromA9 =
  false

NSClayPromotedFromA9IsFalse :
  NSClayPromotedFromA9 ≡ false
NSClayPromotedFromA9IsFalse =
  refl

TerminalPromotionFromA9 : Bool
TerminalPromotionFromA9 =
  false

TerminalPromotionFromA9IsFalse :
  TerminalPromotionFromA9 ≡ false
TerminalPromotionFromA9IsFalse =
  refl

record NSA9CKNBKMClosureBoundary : Set where
  field
    closureClauses :
      List A9ClosureClause
    closureClausesAreCanonical :
      closureClauses ≡ canonicalA9ClosureClauses
    classicalInputs :
      List A9ClassicalInput
    classicalInputsAreCanonical :
      classicalInputs ≡ canonicalA9ClassicalInputs
    downstreamBlockers :
      List DownstreamA9Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA9Blockers
    closureClauseCountIs6 :
      a9ClosureClauseCount ≡ 6
    classicalInputCountIs4 :
      a9ClassicalInputCount ≡ 4
    blockerCountIs3 :
      downstreamA9BlockerCount ≡ 3
    a9StillFalse :
      A9CKNBKMClosureProved ≡ false
    nsClayStillFalse :
      NSClayPromotedFromA9 ≡ false
    terminalStillFalse :
      TerminalPromotionFromA9 ≡ false

canonicalNSA9CKNBKMClosureBoundary :
  NSA9CKNBKMClosureBoundary
canonicalNSA9CKNBKMClosureBoundary =
  record
    { closureClauses =
        canonicalA9ClosureClauses
    ; closureClausesAreCanonical =
        refl
    ; classicalInputs =
        canonicalA9ClassicalInputs
    ; classicalInputsAreCanonical =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA9Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; closureClauseCountIs6 =
        refl
    ; classicalInputCountIs4 =
        refl
    ; blockerCountIs3 =
        refl
    ; a9StillFalse =
        refl
    ; nsClayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

NSA9CKNBKMClosureBoundaryRecorded : Bool
NSA9CKNBKMClosureBoundaryRecorded =
  true

NSA9CKNBKMClosureBoundaryRecordedIsTrue :
  NSA9CKNBKMClosureBoundaryRecorded ≡ true
NSA9CKNBKMClosureBoundaryRecordedIsTrue =
  refl
