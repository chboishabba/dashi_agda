{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.SpatialResidualSecantWeldExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteContinuityResidualExact as Terminal
import DASHI.Physics.Semiconductor.Device.FiniteSecantResponseCorrectionExact as Secant
import DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact as Spatial

------------------------------------------------------------------------
-- SAME-OBJECT WELD
--
-- The earlier finite secant response was calibrated against a contact-relative
-- two-coordinate residual.  The new interior spatial continuity operator now
-- reproduces exactly the same finite score on the admitted source family.
-- Therefore the existing inverse-response correction can be transported onto
-- the spatial residual without inventing a second correction table.
------------------------------------------------------------------------

spatialScoreAgreesWithEarlierResidual :
  (q : Cell.SourceCharge) →
  Spatial.spatialResidualScore q ≡ Terminal.residualScore q
spatialScoreAgreesWithEarlierResidual Cell.q1 = refl
spatialScoreAgreesWithEarlierResidual Cell.q3 = refl
spatialScoreAgreesWithEarlierResidual Cell.q5 = refl

spatialCorrectionMagnitude : Cell.SourceCharge → Nat
spatialCorrectionMagnitude = Secant.correctionMagnitude

-- Existing inverse secant response, now read against the spatial divergence /
-- generation-recombination score:
--
--   3 * delta-q = 2 * spatialResidualScore.
spatialInverseSecantLaw :
  (q : Cell.SourceCharge) →
  spatialCorrectionMagnitude q * 3
    ≡ Spatial.spatialResidualScore q * 2
spatialInverseSecantLaw Cell.q1 = refl
spatialInverseSecantLaw Cell.q3 = refl
spatialInverseSecantLaw Cell.q5 = refl

spatialCorrectedSource : Cell.SourceCharge → Cell.SourceCharge
spatialCorrectedSource = Secant.secantCorrectedSource

spatialCorrectionClosesInteriorContinuity :
  (q : Cell.SourceCharge) →
  Spatial.spatialResidualScore (spatialCorrectedSource q) ≡ 0
spatialCorrectionClosesInteriorContinuity Cell.q1 = refl
spatialCorrectionClosesInteriorContinuity Cell.q3 = refl
spatialCorrectionClosesInteriorContinuity Cell.q5 = refl

spatialCorrectedCell : Cell.SourceCharge → Cell.ComputedCell
spatialCorrectedCell q = Cell.solveCell (spatialCorrectedSource q)

q1SpatialCorrectionRecomputesClosedCell :
  spatialCorrectedCell Cell.q1 ≡ Cell.solveCell Cell.q5
q1SpatialCorrectionRecomputesClosedCell = refl

q3SpatialCorrectionRecomputesClosedCell :
  spatialCorrectedCell Cell.q3 ≡ Cell.solveCell Cell.q5
q3SpatialCorrectionRecomputesClosedCell = refl

q5SpatialCorrectionKeepsClosedCell :
  spatialCorrectedCell Cell.q5 ≡ Cell.solveCell Cell.q5
q5SpatialCorrectionKeepsClosedCell = refl

------------------------------------------------------------------------
-- The spatial closure is stronger in representation than the old scalar score:
-- at q5 both electron and hole interior residual coordinates vanish separately.
------------------------------------------------------------------------

spatialCorrectionElectronResidualZero :
  (q : Cell.SourceCharge) →
  Spatial.electronDivergenceResidual
    (Spatial.spatialResidual (spatialCorrectedSource q)) ≡ 0
spatialCorrectionElectronResidualZero Cell.q1 = refl
spatialCorrectionElectronResidualZero Cell.q3 = refl
spatialCorrectionElectronResidualZero Cell.q5 = refl

spatialCorrectionHoleResidualZero :
  (q : Cell.SourceCharge) →
  Spatial.holeDivergenceResidual
    (Spatial.spatialResidual (spatialCorrectedSource q)) ≡ 0
spatialCorrectionHoleResidualZero Cell.q1 = refl
spatialCorrectionHoleResidualZero Cell.q3 = refl
spatialCorrectionHoleResidualZero Cell.q5 = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data SpatialSecantPhysicalLeaf : Set where
  PhysicalResidualJacobian : SpatialSecantPhysicalLeaf
  PhysicalMeshWeightedNorm : SpatialSecantPhysicalLeaf
  CoupledPoissonContinuityJacobian : SpatialSecantPhysicalLeaf
  DampedSpatialUpdate : SpatialSecantPhysicalLeaf
  MultiCellResidualAssembly : SpatialSecantPhysicalLeaf
  BasinPreservation : SpatialSecantPhysicalLeaf
  PhysicalSpatialConvergence : SpatialSecantPhysicalLeaf

-- Firewalls:
-- score equality on this finite family != identity of residual mechanisms.
-- transported finite secant response != derivative of the physical PDE residual.
-- one-step finite closure != convergence of a spatial semiconductor solver.
