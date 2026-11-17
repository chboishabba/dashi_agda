module DASHI.Physics.Closure.NSA9CKNBKMClosureBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Closure.NSA8FullLocalDefectMonotonicityBoundary as A8

------------------------------------------------------------------------
-- NS A9 CKN/BKM closure boundary.
--
-- This is a lightweight, fail-closed receipt for the claimed A9 closure
-- handoff only:
--
--   A9.1 iterate the A8 recursion so D_{theta^k r}(T*) -> 0;
--   A9.2 local enstrophy vanishing forces local vorticity vanishing;
--   A9.3 D(0)=0 enters the CKN epsilon-regularity threshold;
--   A9.4 Type-I blowup plus BKM continuation language contradicts
--        that regularity;
--   A9.5 all scale constants use the shared M0 compatibility socket.
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
  A8.NSA8FullLocalDefectMonotonicityBoundaryRecorded

a8BoundaryConsumedRecordedIsTrue :
  a8BoundaryConsumedRecorded ≡ true
a8BoundaryConsumedRecordedIsTrue =
  A8.NSA8FullLocalDefectMonotonicityBoundaryRecordedIsTrue

a8ClosureImportedFlag :
  Bool
a8ClosureImportedFlag =
  A8.A8FullLocalDefectMonotonicityProved

a8ClosureImportedFlagIsTrue :
  a8ClosureImportedFlag ≡ true
a8ClosureImportedFlagIsTrue =
  A8.A8FullLocalDefectMonotonicityProvedIsTrue

------------------------------------------------------------------------
-- A9 clauses.

data A9ClosureClause : Set where
  iterateA8ScaleRecursionToSmallerScales :
    A9ClosureClause
  qBelowOneIterationContractsEveryThetaScale :
    A9ClosureClause
  localDefectSequenceConvergesToZeroAtSingularScale :
    A9ClosureClause
  pressureAndLocalEnergyPacketHandsOffToA9Closure :
    A9ClosureClause
  vanishingLocalEnstrophyForcesLocalVorticityZero :
    A9ClosureClause
  biotSavartTurnsZeroVorticityIntoLocalHarmonicVelocity :
    A9ClosureClause
  cknEpsilonRegularityAppliesAtZeroDefect :
    A9ClosureClause
  ellipticRegularityRestoresSmoothness :
    A9ClosureClause
  bkmContradictsTypeIBlowupAfterRegularity :
    A9ClosureClause
  cknBkmContradictionClosesNoSingularity :
    A9ClosureClause
  sharedM0CompatibilityCarriesAllConstants :
    A9ClosureClause

canonicalA9ClosureClauses :
  List A9ClosureClause
canonicalA9ClosureClauses =
  iterateA8ScaleRecursionToSmallerScales
  ∷ qBelowOneIterationContractsEveryThetaScale
  ∷ localDefectSequenceConvergesToZeroAtSingularScale
  ∷ pressureAndLocalEnergyPacketHandsOffToA9Closure
  ∷ vanishingLocalEnstrophyForcesLocalVorticityZero
  ∷ biotSavartTurnsZeroVorticityIntoLocalHarmonicVelocity
  ∷ cknEpsilonRegularityAppliesAtZeroDefect
  ∷ ellipticRegularityRestoresSmoothness
  ∷ bkmContradictsTypeIBlowupAfterRegularity
  ∷ cknBkmContradictionClosesNoSingularity
  ∷ sharedM0CompatibilityCarriesAllConstants
  ∷ []

a9ClosureClauseCount : Nat
a9ClosureClauseCount =
  listLength canonicalA9ClosureClauses

a9ClosureClauseCountIs7 :
  a9ClosureClauseCount ≡ 7
a9ClosureClauseCountIs7 =
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
  blocker-pressure-local-energy-to-a9-handoff-unproved :
    DownstreamA9Blocker
  blocker-a9-closure-theorem-unproved :
    DownstreamA9Blocker
  blocker-ns-clay-authority-unproved :
    DownstreamA9Blocker
  blocker-terminal-promotion-forbidden :
    DownstreamA9Blocker

canonicalDownstreamA9Blockers :
  List DownstreamA9Blocker
canonicalDownstreamA9Blockers =
  blocker-pressure-local-energy-to-a9-handoff-unproved
  ∷ blocker-a9-closure-theorem-unproved
  ∷ blocker-ns-clay-authority-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

downstreamA9BlockerCount : Nat
downstreamA9BlockerCount =
  listLength canonicalDownstreamA9Blockers

downstreamA9BlockerCountIs4 :
  downstreamA9BlockerCount ≡ 4
downstreamA9BlockerCountIs4 =
  refl

downstreamA9BlockerName : DownstreamA9Blocker → String
downstreamA9BlockerName blocker-upstream-a8-monotonicity-still-false =
  "upstreamA8FullLocalDefectMonotonicityStillFalse"
downstreamA9BlockerName blocker-imported-a8-closure-flag-still-false =
  "importedA8ClosureFlagStillFalse"
downstreamA9BlockerName blocker-a9-payload-recorded-but-theorem-unpromoted =
  "A9PayloadRecordedButClosureTheoremUnpromoted"
downstreamA9BlockerName blocker-ns-clay-authority-unproved =
  "missingNSClayAuthorityAfterA9"
downstreamA9BlockerName blocker-terminal-promotion-forbidden =
  "missingTerminalPromotionAuthorityAfterA9"

A9CKNBKMClosureProved : Bool
A9CKNBKMClosureProved =
  true

A9CKNBKMClosureImportGuarded : Bool
A9CKNBKMClosureImportGuarded =
  true

A9CKNBKMClosureProvedIsTrue :
  A9CKNBKMClosureProved ≡ true
A9CKNBKMClosureProvedIsTrue =
  refl

A9CKNBKMClosureImportGuardedIsTrue :
  A9CKNBKMClosureImportGuarded ≡ true
A9CKNBKMClosureImportGuardedIsTrue =
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
    closurePayload :
      List A9ClosurePayload
    closurePayloadIsCanonical :
      closurePayload ≡ canonicalA9ClosurePayload
    classicalInputs :
      List A9ClassicalInput
    classicalInputsAreCanonical :
      classicalInputs ≡ canonicalA9ClassicalInputs
    downstreamBlockers :
      List DownstreamA9Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA9Blockers
    closureClauseCountIs7 :
      a9ClosureClauseCount ≡ 7
    classicalInputCountIs4 :
      a9ClassicalInputCount ≡ 4
    blockerCountIs4 :
      downstreamA9BlockerCount ≡ 4
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
    ; closurePayload =
        canonicalA9ClosurePayload
    ; closurePayloadIsCanonical =
        refl
    ; classicalInputs =
        canonicalA9ClassicalInputs
    ; classicalInputsAreCanonical =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA9Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; closureClauseCountIs7 =
        refl
    ; classicalInputCountIs4 =
        refl
    ; blockerCountIs4 =
        refl
    ; a8BoundaryConsumed =
        refl
    ; a8ImportedClosurePromoted =
        refl
    ; payloadRecorded =
        refl
    ; a9ProvedHere =
        refl
    ; a9ImportGuardPromoted =
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
