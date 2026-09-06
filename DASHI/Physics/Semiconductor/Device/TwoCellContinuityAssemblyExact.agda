{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.TwoCellContinuityAssemblyExact where

------------------------------------------------------------------------
-- SCIENTIFIC SOURCES
--
-- Siegfried Selberherr,
-- "Analysis and Simulation of Semiconductor Devices",
-- Springer Vienna (1984), DOI 10.1007/978-3-7091-8752-4.
--
-- D. L. Scharfetter and H. K. Gummel,
-- "Large-signal analysis of a silicon Read diode oscillator",
-- IEEE Transactions on Electron Devices 16 (1969), 64-77,
-- DOI 10.1109/T-ED.1969.16566.
--
-- The two-cell finite assembly is a DASHI exact fixture.  It is not a reported
-- discretization or parameter set from either source.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact as OneCell
import DASHI.Biology.Physical.FiniteReactionDiffusionConservationExact as RD

------------------------------------------------------------------------
-- Two interior control volumes and three faces:
--
-- boundary L | cell A | shared face | cell B | boundary R
------------------------------------------------------------------------

data InteriorCell : Set where
  cellA cellB : InteriorCell

data AssemblyFace : Set where
  boundaryLeft sharedFace boundaryRight : AssemblyFace

record CarrierControlVolume : Set where
  constructor carrierControlVolume
  field
    electronIn  : Nat
    electronOut : Nat
    holeIn      : Nat
    holeOut     : Nat
    generation  : Nat
    recombination : Nat
    electronResidual : Nat
    holeResidual : Nat

open CarrierControlVolume public

------------------------------------------------------------------------
-- Local cells.
--
-- q1 has a nontrivial source/sink redistribution across the two cells;
-- q3 has neutral G/R locally; q5 is fully closed.  Internal-face currents are
-- shared literally between cell A output and cell B input.
------------------------------------------------------------------------

firstCell : Cell.SourceCharge → CarrierControlVolume
firstCell Cell.q1 = carrierControlVolume 14 12 1 2 2 1 3 0
firstCell Cell.q3 = carrierControlVolume 12 11 2 2 1 1 1 0
firstCell Cell.q5 = carrierControlVolume 10 10 3 3 1 1 0 0

secondCell : Cell.SourceCharge → CarrierControlVolume
secondCell Cell.q1 = carrierControlVolume 12 10 2 3 1 2 1 2
secondCell Cell.q3 = carrierControlVolume 11 10 2 3 1 1 1 1
secondCell Cell.q5 = carrierControlVolume 10 10 3 3 1 1 0 0

------------------------------------------------------------------------
-- Local subtraction-free semiconductor continuity accounting.
--
-- electron: Jout + R + residual = Jin + G
-- hole:     Jin  + G + residual = Jout + R
------------------------------------------------------------------------

firstElectronBalance :
  (q : Cell.SourceCharge) →
  electronOut (firstCell q) + recombination (firstCell q)
    + electronResidual (firstCell q)
  ≡ electronIn (firstCell q) + generation (firstCell q)
firstElectronBalance Cell.q1 = refl
firstElectronBalance Cell.q3 = refl
firstElectronBalance Cell.q5 = refl

firstHoleBalance :
  (q : Cell.SourceCharge) →
  holeIn (firstCell q) + generation (firstCell q)
    + holeResidual (firstCell q)
  ≡ holeOut (firstCell q) + recombination (firstCell q)
firstHoleBalance Cell.q1 = refl
firstHoleBalance Cell.q3 = refl
firstHoleBalance Cell.q5 = refl

secondElectronBalance :
  (q : Cell.SourceCharge) →
  electronOut (secondCell q) + recombination (secondCell q)
    + electronResidual (secondCell q)
  ≡ electronIn (secondCell q) + generation (secondCell q)
secondElectronBalance Cell.q1 = refl
secondElectronBalance Cell.q3 = refl
secondElectronBalance Cell.q5 = refl

secondHoleBalance :
  (q : Cell.SourceCharge) →
  holeIn (secondCell q) + generation (secondCell q)
    + holeResidual (secondCell q)
  ≡ holeOut (secondCell q) + recombination (secondCell q)
secondHoleBalance Cell.q1 = refl
secondHoleBalance Cell.q3 = refl
secondHoleBalance Cell.q5 = refl

------------------------------------------------------------------------
-- Same-object shared-face weld.
------------------------------------------------------------------------

sharedElectronFaceMatches :
  (q : Cell.SourceCharge) →
  electronOut (firstCell q) ≡ electronIn (secondCell q)
sharedElectronFaceMatches Cell.q1 = refl
sharedElectronFaceMatches Cell.q3 = refl
sharedElectronFaceMatches Cell.q5 = refl

sharedHoleFaceMatches :
  (q : Cell.SourceCharge) →
  holeOut (firstCell q) ≡ holeIn (secondCell q)
sharedHoleFaceMatches Cell.q1 = refl
sharedHoleFaceMatches Cell.q3 = refl
sharedHoleFaceMatches Cell.q5 = refl

leftBoundaryElectronMatchesComputedDevice :
  (q : Cell.SourceCharge) →
  electronIn (firstCell q) ≡ Cell.electronCurrent q
leftBoundaryElectronMatchesComputedDevice Cell.q1 = refl
leftBoundaryElectronMatchesComputedDevice Cell.q3 = refl
leftBoundaryElectronMatchesComputedDevice Cell.q5 = refl

leftBoundaryHoleMatchesComputedDevice :
  (q : Cell.SourceCharge) →
  holeIn (firstCell q) ≡ Cell.holeCurrent q
leftBoundaryHoleMatchesComputedDevice Cell.q1 = refl
leftBoundaryHoleMatchesComputedDevice Cell.q3 = refl
leftBoundaryHoleMatchesComputedDevice Cell.q5 = refl

------------------------------------------------------------------------
-- Local and assembled residuals.
------------------------------------------------------------------------

cellResidualScore : CarrierControlVolume → Nat
cellResidualScore cell = electronResidual cell + holeResidual cell

assemblyResidualScore : Cell.SourceCharge → Nat
assemblyResidualScore q =
  cellResidualScore (firstCell q) + cellResidualScore (secondCell q)

q1FirstCellResidual : cellResidualScore (firstCell Cell.q1) ≡ 3
q1FirstCellResidual = refl

q1SecondCellResidual : cellResidualScore (secondCell Cell.q1) ≡ 3
q1SecondCellResidual = refl

q3FirstCellResidual : cellResidualScore (firstCell Cell.q3) ≡ 1
q3FirstCellResidual = refl

q3SecondCellResidual : cellResidualScore (secondCell Cell.q3) ≡ 2
q3SecondCellResidual = refl

q5FirstCellResidual : cellResidualScore (firstCell Cell.q5) ≡ 0
q5FirstCellResidual = refl

q5SecondCellResidual : cellResidualScore (secondCell Cell.q5) ≡ 0
q5SecondCellResidual = refl

q1AssemblyResidual : assemblyResidualScore Cell.q1 ≡ 6
q1AssemblyResidual = refl

q3AssemblyResidual : assemblyResidualScore Cell.q3 ≡ 3
q3AssemblyResidual = refl

q5AssemblyResidual : assemblyResidualScore Cell.q5 ≡ 0
q5AssemblyResidual = refl

------------------------------------------------------------------------
-- The two-cell assembly refines the one-cell spatial score without changing
-- the admitted global residual magnitude.
------------------------------------------------------------------------

assemblyAgreesWithOneCellSpatialScore :
  (q : Cell.SourceCharge) →
  assemblyResidualScore q ≡ OneCell.spatialResidualScore q
assemblyAgreesWithOneCellSpatialScore Cell.q1 = refl
assemblyAgreesWithOneCellSpatialScore Cell.q3 = refl
assemblyAgreesWithOneCellSpatialScore Cell.q5 = refl

------------------------------------------------------------------------
-- Cross-pollination donor: exact conservative transport exists elsewhere in
-- the repo and is carried here as the generic internal-transfer architecture.
------------------------------------------------------------------------

finiteTransportConservationDonor :
  (x : RD.TwoCompartment) →
  RD.totalMaterial (RD.diffuseLeftToRight x) ≡ RD.totalMaterial x
finiteTransportConservationDonor = RD.diffusionConservesTotal

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data TwoCellPhysicalLeaf : Set where
  GeometricFaceMetric : TwoCellPhysicalLeaf
  CellVolumeWeights : TwoCellPhysicalLeaf
  PhysicalScharfetterGummelFlux : TwoCellPhysicalLeaf
  PhysicalGenerationRecombination : TwoCellPhysicalLeaf
  NonuniformMesh : TwoCellPhysicalLeaf
  MoreThanTwoInteriorCells : TwoCellPhysicalLeaf
  GlobalSparseContinuityOperator : TwoCellPhysicalLeaf
  PhysicalBoundaryFluxes : TwoCellPhysicalLeaf

-- Firewalls:
-- shared-face equality in this finite fixture != conservative SI discretization.
-- local residual decomposition != physical mesh convergence.
-- two-cell global score != norm of a production sparse residual vector.
