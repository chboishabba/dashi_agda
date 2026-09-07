{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ResidualDrivenComputedCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell

------------------------------------------------------------------------
-- RESIDUAL-DRIVEN COMPUTED DEVICE CORRECTION
--
-- The previous owner made (phi,n,p,Jn,Jp) computed from the source coordinate,
-- but its q1 -> q3 -> q5 correction was still an explicit lookup table.
-- Here the selected correction is routed through a residual extracted from the
-- already-computed electrical state:
--
--   q -> solveCell q -> (Jn + Jp) mismatch -> admitted action -> q' -> solveCell q'.
--
-- This is still a normalized finite fixture.  The target-current condition and
-- correction response are not claimed as a physical semiconductor residual law.
------------------------------------------------------------------------

targetTotalCurrent : Nat
targetTotalCurrent = 13

totalCurrent : Cell.SourceCharge → Nat
totalCurrent q = Cell.electronCurrent q + Cell.holeCurrent q

data CurrentMismatch : Set where
  overByTwo overByOne balanced : CurrentMismatch

mismatchCode : CurrentMismatch → Nat
mismatchCode overByTwo = 2
mismatchCode overByOne = 1
mismatchCode balanced = 0

currentMismatch : Cell.SourceCharge → CurrentMismatch
currentMismatch Cell.q1 = overByTwo
currentMismatch Cell.q3 = overByOne
currentMismatch Cell.q5 = balanced

currentMismatchAccounting :
  (q : Cell.SourceCharge) →
  targetTotalCurrent + mismatchCode (currentMismatch q) ≡ totalCurrent q
currentMismatchAccounting Cell.q1 = refl
currentMismatchAccounting Cell.q3 = refl
currentMismatchAccounting Cell.q5 = refl

q1ComputedTotal : totalCurrent Cell.q1 ≡ 15
q1ComputedTotal = refl

q3ComputedTotal : totalCurrent Cell.q3 ≡ 14
q3ComputedTotal = refl

q5ComputedTotal : totalCurrent Cell.q5 ≡ 13
q5ComputedTotal = refl

------------------------------------------------------------------------
-- Residual -> action policy.
------------------------------------------------------------------------

data CorrectionAction : Set where
  strongCurrentCorrection mildCurrentCorrection holdBalanced : CorrectionAction

actionForResidual : CurrentMismatch → CorrectionAction
actionForResidual overByTwo = strongCurrentCorrection
actionForResidual overByOne = mildCurrentCorrection
actionForResidual balanced = holdBalanced

selectedAction : Cell.SourceCharge → CorrectionAction
selectedAction q = actionForResidual (currentMismatch q)

data CorrectionPrecondition : Cell.SourceCharge → CorrectionAction → Set where
  strongNeeded : CorrectionPrecondition Cell.q1 strongCurrentCorrection
  mildNeeded : CorrectionPrecondition Cell.q3 mildCurrentCorrection
  balancedCanHold : CorrectionPrecondition Cell.q5 holdBalanced

data CorrectionPostcondition :
  Cell.SourceCharge → CorrectionAction → Cell.SourceCharge → Set where
  strongRaisesToQ3 :
    CorrectionPostcondition Cell.q1 strongCurrentCorrection Cell.q3
  mildRaisesToQ5 :
    CorrectionPostcondition Cell.q3 mildCurrentCorrection Cell.q5
  balancedStaysQ5 :
    CorrectionPostcondition Cell.q5 holdBalanced Cell.q5

correctionActionLabel : CorrectionAction → String
correctionActionLabel strongCurrentCorrection = "strong finite current-residual correction"
correctionActionLabel mildCurrentCorrection = "mild finite current-residual correction"
correctionActionLabel holdBalanced = "hold current-balanced finite state"

correctionSystem :
  Dependency.DependentActionSystem Cell.SourceCharge CorrectionAction
correctionSystem = record
  { Precondition = CorrectionPrecondition
  ; Postcondition = CorrectionPostcondition
  ; actionLabel = correctionActionLabel
  }

admittedCorrection :
  (q : Cell.SourceCharge) →
  Dependency.AdmissibleAction correctionSystem q (selectedAction q)
admittedCorrection Cell.q1 = record
  { precondition = strongNeeded
  ; after = Cell.q3
  ; postcondition = strongRaisesToQ3
  ; dependencyReceipt = "computed total-current excess 2 selects the admitted strong correction"
  }
admittedCorrection Cell.q3 = record
  { precondition = mildNeeded
  ; after = Cell.q5
  ; postcondition = mildRaisesToQ5
  ; dependencyReceipt = "computed total-current excess 1 selects the admitted mild correction"
  }
admittedCorrection Cell.q5 = record
  { precondition = balancedCanHold
  ; after = Cell.q5
  ; postcondition = balancedStaysQ5
  ; dependencyReceipt = "zero computed total-current excess admits the hold action"
  }

residualDrivenStep : Cell.SourceCharge → Cell.SourceCharge
residualDrivenStep q = Dependency.after (admittedCorrection q)

residualDrivenStepAgreesWithOldCorrection :
  (q : Cell.SourceCharge) →
  residualDrivenStep q ≡ Cell.chargeCorrection q
residualDrivenStepAgreesWithOldCorrection Cell.q1 = refl
residualDrivenStepAgreesWithOldCorrection Cell.q3 = refl
residualDrivenStepAgreesWithOldCorrection Cell.q5 = refl

residualDrivenCellStep : Cell.SourceCharge → Cell.ComputedCell
residualDrivenCellStep q = Cell.solveCell (residualDrivenStep q)

q1ResidualStep : residualDrivenCellStep Cell.q1 ≡ Cell.solveCell Cell.q3
q1ResidualStep = refl

q3ResidualStep : residualDrivenCellStep Cell.q3 ≡ Cell.solveCell Cell.q5
q3ResidualStep = refl

q5ResidualStep : residualDrivenCellStep Cell.q5 ≡ Cell.solveCell Cell.q5
q5ResidualStep = refl

q1ResidualLoopClosesInTwo :
  residualDrivenStep (residualDrivenStep Cell.q1) ≡ Cell.q5
q1ResidualLoopClosesInTwo = refl

------------------------------------------------------------------------
-- Cross-pollination with ResidualObserverDependencyExact.
------------------------------------------------------------------------

currentResidualScore : Residual.ResidualStateScore Cell.SourceCharge
currentResidualScore q = mismatchCode (currentMismatch q)

admittedCorrectionDoesNotIncreaseResidual :
  (q : Cell.SourceCharge) →
  Residual.Decouples currentResidualScore (admittedCorrection q)
admittedCorrectionDoesNotIncreaseResidual Cell.q1 = s≤s z≤n
admittedCorrectionDoesNotIncreaseResidual Cell.q3 = z≤n
admittedCorrectionDoesNotIncreaseResidual Cell.q5 = z≤n

q1ScoreDropsTwoToOne :
  currentResidualScore (residualDrivenStep Cell.q1) ≡ 1
q1ScoreDropsTwoToOne = refl

q3ScoreDropsOneToZero :
  currentResidualScore (residualDrivenStep Cell.q3) ≡ 0
q3ScoreDropsOneToZero = refl

q5ScoreRemainsZero :
  currentResidualScore (residualDrivenStep Cell.q5) ≡ 0
q5ScoreRemainsZero = refl

------------------------------------------------------------------------
-- Closure is itself computed from the solved electrical residual.
------------------------------------------------------------------------

data ResidualClosed : Cell.SourceCharge → Set where
  q5Closed : ResidualClosed Cell.q5

closedImpliesBalanced :
  (q : Cell.SourceCharge) →
  ResidualClosed q →
  currentMismatch q ≡ balanced
closedImpliesBalanced Cell.q5 q5Closed = refl

balancedImpliesFixed :
  (q : Cell.SourceCharge) →
  currentMismatch q ≡ balanced →
  residualDrivenStep q ≡ q
balancedImpliesFixed Cell.q1 ()
balancedImpliesFixed Cell.q3 ()
balancedImpliesFixed Cell.q5 refl = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data ResidualCorrectionPhysicalLeaf : Set where
  PhysicalCurrentContinuityResidual : ResidualCorrectionPhysicalLeaf
  SignedElectronHoleCurrentConvention : ResidualCorrectionPhysicalLeaf
  PhysicalContactCurrentTarget : ResidualCorrectionPhysicalLeaf
  PhysicalResidualJacobian : ResidualCorrectionPhysicalLeaf
  PhysicalDampedUpdateLaw : ResidualCorrectionPhysicalLeaf
  PhysicalActionAdmissibility : ResidualCorrectionPhysicalLeaf
  SameObjectResidualContraction : ResidualCorrectionPhysicalLeaf

-- Firewalls:
-- Jn+Jp=13 in this normalized fixture != a physical contact/continuity law.
-- residual classification != authority to change a device state.
-- admissible finite action != Newton/Gummel Jacobian update.
-- residual non-increase on this finite family != physical solver convergence.
