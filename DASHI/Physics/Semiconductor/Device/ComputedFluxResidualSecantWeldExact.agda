{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ComputedFluxResidualSecantWeldExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_*_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.ComputedFluxTwoCellContinuityExact as Computed
import DASHI.Physics.Semiconductor.Device.FiniteSecantResponseCorrectionExact as Secant

------------------------------------------------------------------------
-- COMPUTED-FLUX RESIDUAL -> SECANT CORRECTION WELD
--
-- The secant correction is now consumed against the score produced downstream
-- of nodal state -> finite SG face flux -> local continuity residual -> assembly.
-- The earlier residual tables are no longer required to state the correction
-- equation in this owner.
------------------------------------------------------------------------

computedAssemblyScoreMatchesSecantFamily :
  (q : Cell.SourceCharge) →
  Computed.computedAssemblyResidualScore q
    ≡ Secant.residualClassCode (Secant.residualClass q)
computedAssemblyScoreMatchesSecantFamily Cell.q1 = refl
computedAssemblyScoreMatchesSecantFamily Cell.q3 = refl
computedAssemblyScoreMatchesSecantFamily Cell.q5 = refl

computedFluxInverseSecantLaw :
  (q : Cell.SourceCharge) →
  Secant.correctionMagnitude q * 3
    ≡ Computed.computedAssemblyResidualScore q * 2
computedFluxInverseSecantLaw Cell.q1 = refl
computedFluxInverseSecantLaw Cell.q3 = refl
computedFluxInverseSecantLaw Cell.q5 = refl

computedFluxCorrectedSource : Cell.SourceCharge → Cell.SourceCharge
computedFluxCorrectedSource = Secant.secantCorrectedSource

computedFluxCorrectionClosesAssembly :
  (q : Cell.SourceCharge) →
  Computed.computedAssemblyResidualScore (computedFluxCorrectedSource q) ≡ 0
computedFluxCorrectionClosesAssembly Cell.q1 = refl
computedFluxCorrectionClosesAssembly Cell.q3 = refl
computedFluxCorrectionClosesAssembly Cell.q5 = refl

------------------------------------------------------------------------
-- Strong local closure: every carrier residual in both control volumes closes.
------------------------------------------------------------------------

correctedCellAElectronResidualZero :
  (q : Cell.SourceCharge) →
  Computed.electronResidualA (computedFluxCorrectedSource q) ≡ 0
correctedCellAElectronResidualZero Cell.q1 = refl
correctedCellAElectronResidualZero Cell.q3 = refl
correctedCellAElectronResidualZero Cell.q5 = refl

correctedCellAHoleResidualZero :
  (q : Cell.SourceCharge) →
  Computed.holeResidualA (computedFluxCorrectedSource q) ≡ 0
correctedCellAHoleResidualZero Cell.q1 = refl
correctedCellAHoleResidualZero Cell.q3 = refl
correctedCellAHoleResidualZero Cell.q5 = refl

correctedCellBElectronResidualZero :
  (q : Cell.SourceCharge) →
  Computed.electronResidualB (computedFluxCorrectedSource q) ≡ 0
correctedCellBElectronResidualZero Cell.q1 = refl
correctedCellBElectronResidualZero Cell.q3 = refl
correctedCellBElectronResidualZero Cell.q5 = refl

correctedCellBHoleResidualZero :
  (q : Cell.SourceCharge) →
  Computed.holeResidualB (computedFluxCorrectedSource q) ≡ 0
correctedCellBHoleResidualZero Cell.q1 = refl
correctedCellBHoleResidualZero Cell.q3 = refl
correctedCellBHoleResidualZero Cell.q5 = refl

------------------------------------------------------------------------
-- Recompute the original same-object electrical cell after the correction.
------------------------------------------------------------------------

correctedComputedCell : Cell.SourceCharge → Cell.ComputedCell
correctedComputedCell q = Cell.solveCell (computedFluxCorrectedSource q)

q1ComputedFluxCorrectionReachesClosedCell :
  correctedComputedCell Cell.q1 ≡ Cell.solveCell Cell.q5
q1ComputedFluxCorrectionReachesClosedCell = refl

q3ComputedFluxCorrectionReachesClosedCell :
  correctedComputedCell Cell.q3 ≡ Cell.solveCell Cell.q5
q3ComputedFluxCorrectionReachesClosedCell = refl

q5ComputedFluxCorrectionKeepsClosedCell :
  correctedComputedCell Cell.q5 ≡ Cell.solveCell Cell.q5
q5ComputedFluxCorrectionKeepsClosedCell = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data ComputedFluxSecantPhysicalLeaf : Set where
  PhysicalBernoulliJacobian : ComputedFluxSecantPhysicalLeaf
  SparseFluxDerivativeBlocks : ComputedFluxSecantPhysicalLeaf
  SignedResidualNorm : ComputedFluxSecantPhysicalLeaf
  DampingOrLineSearch : ComputedFluxSecantPhysicalLeaf
  BasinPreservation : ComputedFluxSecantPhysicalLeaf
  PhysicalNewtonGummelUpdate : ComputedFluxSecantPhysicalLeaf

-- Firewall:
-- exact one-step closure of this finite calibrated family != a physical sparse
-- Newton/Gummel convergence theorem.
