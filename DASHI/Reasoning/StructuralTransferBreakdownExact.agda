module DASHI.Reasoning.StructuralTransferBreakdownExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BOUNDED STRUCTURAL TRANSFER
--
-- A structural frame may illuminate one target slice while failing on another.
-- The failure can be informative about the target: the target may no longer
-- instantiate the recoverability/invariance relation presupposed by the frame.
--
-- This is an original DASHI formalisation.  Nusrat Fatima (2026),
-- "Continuity and Its Limits: Toward a Critical Theory of Literary Topology in
-- Shakespeare", DOI 10.46809/jcsll.v7i2.430, motivates the bounded-method
-- reading for literary topology; Fatima is not credited with these Agda
-- records or factorisation-style theorem interfaces.
------------------------------------------------------------------------

data TransferStatus : Set where
  structurallyFitting structurallyBroken : TransferStatus

record StructuralTransferSurface : Set₁ where
  field
    SourceFrame : Set
    Target : Set
    Invariant : Set

    transferStatus : SourceFrame → Target → TransferStatus
    invariantAt : Target → Invariant
    recoverable : Target → Set
    ruptured : Target → Set

    surfaceReading : String

open StructuralTransferSurface public

record FitWitness
    (surface : StructuralTransferSurface) : Set where
  field
    fitFrame : SourceFrame surface
    fitTarget : Target surface
    fitStatus : transferStatus surface fitFrame fitTarget ≡ structurallyFitting
    fitRecoverable : recoverable surface fitTarget

open FitWitness public

record RuptureWitness
    (surface : StructuralTransferSurface) : Set where
  field
    ruptureFrame : SourceFrame surface
    ruptureTarget : Target surface
    ruptureStatus : transferStatus surface ruptureFrame ruptureTarget ≡ structurallyBroken
    ruptureReceipt : ruptured surface ruptureTarget

open RuptureWitness public

record FitHereBreaksThere
    (surface : StructuralTransferSurface) : Set where
  field
    fitting : FitWitness surface
    broken : RuptureWitness surface

open FitHereBreaksThere public

------------------------------------------------------------------------
-- Continuity without sameness / return without reset.
------------------------------------------------------------------------

record ContinuityWithoutSameness : Set₁ where
  field
    State : Set
    start end : State
    Related : State → State → Set
    retainedRelation : Related start end
    notReset : start ≡ end → ⊥
    continuityReading : String

open ContinuityWithoutSameness public

------------------------------------------------------------------------
-- Exact finite specimen: one frame fits a recoverable target and fails after
-- rupture.  This proves only the finite boundary, not a universal theory of
-- literature, trauma, ethics, or topology.
------------------------------------------------------------------------

data ToyFrame : Set where
  continuityFrame : ToyFrame

data ToyTarget : Set where
  deformedRecoverable terminalRupture : ToyTarget

data ToyInvariant : Set where
  retainedConnection lostConnection : ToyInvariant

data RecoverableReceipt : ToyTarget → Set where
  recoverableDeformation : RecoverableReceipt deformedRecoverable

data RuptureReceipt : ToyTarget → Set where
  terminalTear : RuptureReceipt terminalRupture

statusToy : ToyFrame → ToyTarget → TransferStatus
statusToy continuityFrame deformedRecoverable = structurallyFitting
statusToy continuityFrame terminalRupture = structurallyBroken

invariantToy : ToyTarget → ToyInvariant
invariantToy deformedRecoverable = retainedConnection
invariantToy terminalRupture = lostConnection

toySurface : StructuralTransferSurface
toySurface =
  record
    { SourceFrame = ToyFrame
    ; Target = ToyTarget
    ; Invariant = ToyInvariant
    ; transferStatus = statusToy
    ; invariantAt = invariantToy
    ; recoverable = RecoverableReceipt
    ; ruptured = RuptureReceipt
    ; surfaceReading =
        "The same continuity-oriented structural frame fits a recoverable deformation and fails on a terminal rupture."
    }

toyFit : FitWitness toySurface
toyFit =
  record
    { fitFrame = continuityFrame
    ; fitTarget = deformedRecoverable
    ; fitStatus = refl
    ; fitRecoverable = recoverableDeformation
    }

toyBreak : RuptureWitness toySurface
toyBreak =
  record
    { ruptureFrame = continuityFrame
    ; ruptureTarget = terminalRupture
    ; ruptureStatus = refl
    ; ruptureReceipt = terminalTear
    }

toyUsefulHereBreaksThere : FitHereBreaksThere toySurface
toyUsefulHereBreaksThere =
  record
    { fitting = toyFit
    ; broken = toyBreak
    }

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record StructuralTransferBreakdownBoundary : Set where
  constructor structuralTransferBreakdownBoundary
  field
    fitnessOnOneTargetImpliesUniversalFitness : Bool
    fitnessOnOneTargetImpliesUniversalFitnessIsFalse :
      fitnessOnOneTargetImpliesUniversalFitness ≡ false

    ruptureIsMerelyFailureOfAnalystImagination : Bool
    ruptureIsMerelyFailureOfAnalystImaginationIsFalse :
      ruptureIsMerelyFailureOfAnalystImagination ≡ false

    failedTransferMayDiagnoseTargetIncompatibility : Bool
    failedTransferMayDiagnoseTargetIncompatibilityIsTrue :
      failedTransferMayDiagnoseTargetIncompatibility ≡ true

    continuityMeansIdentity : Bool
    continuityMeansIdentityIsFalse :
      continuityMeansIdentity ≡ false

    returnMeansReset : Bool
    returnMeansResetIsFalse :
      returnMeansReset ≡ false

canonicalStructuralTransferBreakdownBoundary :
  StructuralTransferBreakdownBoundary
canonicalStructuralTransferBreakdownBoundary =
  structuralTransferBreakdownBoundary
    false refl
    false refl
    true refl
    false refl
    false refl
