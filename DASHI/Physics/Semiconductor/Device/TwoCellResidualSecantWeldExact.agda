{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.TwoCellResidualSecantWeldExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteSecantResponseCorrectionExact as Secant
import DASHI.Physics.Semiconductor.Device.TwoCellContinuityAssemblyExact as Assembly

------------------------------------------------------------------------
-- The secant correction is now paid by the assembled local continuity residual,
-- not merely by a terminal or single-control-volume score.
------------------------------------------------------------------------

twoCellCorrectionMagnitude : Cell.SourceCharge → Nat
twoCellCorrectionMagnitude = Secant.correctionMagnitude

twoCellInverseSecantLaw :
  (q : Cell.SourceCharge) →
  twoCellCorrectionMagnitude q * 3
    ≡ Assembly.assemblyResidualScore q * 2
twoCellInverseSecantLaw Cell.q1 = refl
twoCellInverseSecantLaw Cell.q3 = refl
twoCellInverseSecantLaw Cell.q5 = refl

twoCellCorrectedSource : Cell.SourceCharge → Cell.SourceCharge
twoCellCorrectedSource = Secant.secantCorrectedSource

twoCellCorrectionClosesAssemblyResidual :
  (q : Cell.SourceCharge) →
  Assembly.assemblyResidualScore (twoCellCorrectedSource q) ≡ 0
twoCellCorrectionClosesAssemblyResidual Cell.q1 = refl
twoCellCorrectionClosesAssemblyResidual Cell.q3 = refl
twoCellCorrectionClosesAssemblyResidual Cell.q5 = refl

------------------------------------------------------------------------
-- Closure is local in every admitted interior cell, not only global after sum.
------------------------------------------------------------------------

correctedFirstCellElectronResidualZero :
  (q : Cell.SourceCharge) →
  Assembly.electronResidual
    (Assembly.firstCell (twoCellCorrectedSource q)) ≡ 0
correctedFirstCellElectronResidualZero Cell.q1 = refl
correctedFirstCellElectronResidualZero Cell.q3 = refl
correctedFirstCellElectronResidualZero Cell.q5 = refl

correctedFirstCellHoleResidualZero :
  (q : Cell.SourceCharge) →
  Assembly.holeResidual
    (Assembly.firstCell (twoCellCorrectedSource q)) ≡ 0
correctedFirstCellHoleResidualZero Cell.q1 = refl
correctedFirstCellHoleResidualZero Cell.q3 = refl
correctedFirstCellHoleResidualZero Cell.q5 = refl

correctedSecondCellElectronResidualZero :
  (q : Cell.SourceCharge) →
  Assembly.electronResidual
    (Assembly.secondCell (twoCellCorrectedSource q)) ≡ 0
correctedSecondCellElectronResidualZero Cell.q1 = refl
correctedSecondCellElectronResidualZero Cell.q3 = refl
correctedSecondCellElectronResidualZero Cell.q5 = refl

correctedSecondCellHoleResidualZero :
  (q : Cell.SourceCharge) →
  Assembly.holeResidual
    (Assembly.secondCell (twoCellCorrectedSource q)) ≡ 0
correctedSecondCellHoleResidualZero Cell.q1 = refl
correctedSecondCellHoleResidualZero Cell.q3 = refl
correctedSecondCellHoleResidualZero Cell.q5 = refl

correctedSharedElectronFaceStillWelded :
  (q : Cell.SourceCharge) →
  Assembly.electronOut (Assembly.firstCell (twoCellCorrectedSource q))
    ≡ Assembly.electronIn (Assembly.secondCell (twoCellCorrectedSource q))
correctedSharedElectronFaceStillWelded q =
  Assembly.sharedElectronFaceMatches (twoCellCorrectedSource q)

correctedSharedHoleFaceStillWelded :
  (q : Cell.SourceCharge) →
  Assembly.holeOut (Assembly.firstCell (twoCellCorrectedSource q))
    ≡ Assembly.holeIn (Assembly.secondCell (twoCellCorrectedSource q))
correctedSharedHoleFaceStillWelded q =
  Assembly.sharedHoleFaceMatches (twoCellCorrectedSource q)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data TwoCellSecantPhysicalLeaf : Set where
  SparseJacobianAssembly : TwoCellSecantPhysicalLeaf
  CellwiseJacobianBlocks : TwoCellSecantPhysicalLeaf
  PhysicalLineSearch : TwoCellSecantPhysicalLeaf
  MeshWeightedResidualNorm : TwoCellSecantPhysicalLeaf
  ConservativeNewtonUpdate : TwoCellSecantPhysicalLeaf
  PhysicalMultiCellConvergence : TwoCellSecantPhysicalLeaf

-- Firewalls:
-- exact local closure on two synthetic cells != physical PDE solver convergence.
-- reuse of one scalar secant slope != inversion of a sparse block Jacobian.
