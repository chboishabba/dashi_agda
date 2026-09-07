{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.ComputedFluxTwoCellContinuityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_∸_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as SG
import DASHI.Physics.Semiconductor.Device.TwoCellContinuityAssemblyExact as Old

------------------------------------------------------------------------
-- COMPUTED TWO-CELL CONTINUITY ASSEMBLY
--
-- Face currents are no longer fields of the assembly.  They are produced by
-- FiniteScharfetterGummelFluxExact from nodal potentials/populations and the
-- finite Bernoulli calibration.  Local continuity residuals are then computed
-- from those face fluxes and the declared generation/recombination coordinates.
--
-- The earlier TwoCellContinuityAssemblyExact remains only a regression target.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Finite source/sink coordinates for each interior control volume.
------------------------------------------------------------------------

generationA : Cell.SourceCharge → Nat
generationA Cell.q1 = 2
generationA Cell.q3 = 1
generationA Cell.q5 = 1

recombinationA : Cell.SourceCharge → Nat
recombinationA Cell.q1 = 1
recombinationA Cell.q3 = 1
recombinationA Cell.q5 = 1

generationB : Cell.SourceCharge → Nat
generationB Cell.q1 = 1
generationB Cell.q3 = 1
generationB Cell.q5 = 1

recombinationB : Cell.SourceCharge → Nat
recombinationB Cell.q1 = 2
recombinationB Cell.q3 = 1
recombinationB Cell.q5 = 1

------------------------------------------------------------------------
-- Local residual producers.
--
-- Electron balance target:
--   Jout + R = Jin + G
-- residual = (Jin + G) monus (Jout + R).
--
-- Hole balance target:
--   Jin + G = Jout + R
-- residual = (Jout + R) monus (Jin + G).
------------------------------------------------------------------------

electronResidualA : Cell.SourceCharge → Nat
electronResidualA q =
  (SG.electronFaceFlux q SG.face01 + generationA q)
  ∸ (SG.electronFaceFlux q SG.face12 + recombinationA q)

holeResidualA : Cell.SourceCharge → Nat
holeResidualA q =
  (SG.holeFaceFlux q SG.face12 + recombinationA q)
  ∸ (SG.holeFaceFlux q SG.face01 + generationA q)

electronResidualB : Cell.SourceCharge → Nat
electronResidualB q =
  (SG.electronFaceFlux q SG.face12 + generationB q)
  ∸ (SG.electronFaceFlux q SG.face23 + recombinationB q)

holeResidualB : Cell.SourceCharge → Nat
holeResidualB q =
  (SG.holeFaceFlux q SG.face23 + recombinationB q)
  ∸ (SG.holeFaceFlux q SG.face12 + generationB q)

------------------------------------------------------------------------
-- Exact local balance receipts.
------------------------------------------------------------------------

cellAElectronBalance :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face12 + recombinationA q
    + electronResidualA q
  ≡ SG.electronFaceFlux q SG.face01 + generationA q
cellAElectronBalance Cell.q1 = refl
cellAElectronBalance Cell.q3 = refl
cellAElectronBalance Cell.q5 = refl

cellAHoleBalance :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face01 + generationA q
    + holeResidualA q
  ≡ SG.holeFaceFlux q SG.face12 + recombinationA q
cellAHoleBalance Cell.q1 = refl
cellAHoleBalance Cell.q3 = refl
cellAHoleBalance Cell.q5 = refl

cellBElectronBalance :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face23 + recombinationB q
    + electronResidualB q
  ≡ SG.electronFaceFlux q SG.face12 + generationB q
cellBElectronBalance Cell.q1 = refl
cellBElectronBalance Cell.q3 = refl
cellBElectronBalance Cell.q5 = refl

cellBHoleBalance :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face12 + generationB q
    + holeResidualB q
  ≡ SG.holeFaceFlux q SG.face23 + recombinationB q
cellBHoleBalance Cell.q1 = refl
cellBHoleBalance Cell.q3 = refl
cellBHoleBalance Cell.q5 = refl

------------------------------------------------------------------------
-- Same-object internal face is automatic: both cells consume the same face12
-- producer rather than copying an internal current value into two records.
------------------------------------------------------------------------

sharedElectronFaceSameObject :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face12 ≡ SG.electronFaceFlux q SG.face12
sharedElectronFaceSameObject q = refl

sharedHoleFaceSameObject :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face12 ≡ SG.holeFaceFlux q SG.face12
sharedHoleFaceSameObject q = refl

------------------------------------------------------------------------
-- Executable local residual decomposition.
------------------------------------------------------------------------

q1ElectronResidualA : electronResidualA Cell.q1 ≡ 3
q1ElectronResidualA = refl
q1HoleResidualA : holeResidualA Cell.q1 ≡ 0
q1HoleResidualA = refl
q1ElectronResidualB : electronResidualB Cell.q1 ≡ 1
q1ElectronResidualB = refl
q1HoleResidualB : holeResidualB Cell.q1 ≡ 2
q1HoleResidualB = refl

q3ElectronResidualA : electronResidualA Cell.q3 ≡ 1
q3ElectronResidualA = refl
q3HoleResidualA : holeResidualA Cell.q3 ≡ 0
q3HoleResidualA = refl
q3ElectronResidualB : electronResidualB Cell.q3 ≡ 1
q3ElectronResidualB = refl
q3HoleResidualB : holeResidualB Cell.q3 ≡ 1
q3HoleResidualB = refl

q5ElectronResidualA : electronResidualA Cell.q5 ≡ 0
q5ElectronResidualA = refl
q5HoleResidualA : holeResidualA Cell.q5 ≡ 0
q5HoleResidualA = refl
q5ElectronResidualB : electronResidualB Cell.q5 ≡ 0
q5ElectronResidualB = refl
q5HoleResidualB : holeResidualB Cell.q5 ≡ 0
q5HoleResidualB = refl

cellAResidualScore : Cell.SourceCharge → Nat
cellAResidualScore q = electronResidualA q + holeResidualA q

cellBResidualScore : Cell.SourceCharge → Nat
cellBResidualScore q = electronResidualB q + holeResidualB q

computedAssemblyResidualScore : Cell.SourceCharge → Nat
computedAssemblyResidualScore q = cellAResidualScore q + cellBResidualScore q

q1ComputedAssemblyResidual : computedAssemblyResidualScore Cell.q1 ≡ 6
q1ComputedAssemblyResidual = refl

q3ComputedAssemblyResidual : computedAssemblyResidualScore Cell.q3 ≡ 3
q3ComputedAssemblyResidual = refl

q5ComputedAssemblyResidual : computedAssemblyResidualScore Cell.q5 ≡ 0
q5ComputedAssemblyResidual = refl

------------------------------------------------------------------------
-- Regression against the historical hand-written two-cell fixture.
-- Direction of authority is now new computed producer -> old table agreement.
------------------------------------------------------------------------

computedScoreAgreesWithOldAssembly :
  (q : Cell.SourceCharge) →
  computedAssemblyResidualScore q ≡ Old.assemblyResidualScore q
computedScoreAgreesWithOldAssembly Cell.q1 = refl
computedScoreAgreesWithOldAssembly Cell.q3 = refl
computedScoreAgreesWithOldAssembly Cell.q5 = refl

computedLeftElectronFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face01 ≡ Old.electronIn (Old.firstCell q)
computedLeftElectronFluxAgreesWithOld Cell.q1 = refl
computedLeftElectronFluxAgreesWithOld Cell.q3 = refl
computedLeftElectronFluxAgreesWithOld Cell.q5 = refl

computedSharedElectronFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face12 ≡ Old.electronOut (Old.firstCell q)
computedSharedElectronFluxAgreesWithOld Cell.q1 = refl
computedSharedElectronFluxAgreesWithOld Cell.q3 = refl
computedSharedElectronFluxAgreesWithOld Cell.q5 = refl

computedRightElectronFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.electronFaceFlux q SG.face23 ≡ Old.electronOut (Old.secondCell q)
computedRightElectronFluxAgreesWithOld Cell.q1 = refl
computedRightElectronFluxAgreesWithOld Cell.q3 = refl
computedRightElectronFluxAgreesWithOld Cell.q5 = refl

computedLeftHoleFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face01 ≡ Old.holeIn (Old.firstCell q)
computedLeftHoleFluxAgreesWithOld Cell.q1 = refl
computedLeftHoleFluxAgreesWithOld Cell.q3 = refl
computedLeftHoleFluxAgreesWithOld Cell.q5 = refl

computedSharedHoleFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face12 ≡ Old.holeOut (Old.firstCell q)
computedSharedHoleFluxAgreesWithOld Cell.q1 = refl
computedSharedHoleFluxAgreesWithOld Cell.q3 = refl
computedSharedHoleFluxAgreesWithOld Cell.q5 = refl

computedRightHoleFluxAgreesWithOld :
  (q : Cell.SourceCharge) →
  SG.holeFaceFlux q SG.face23 ≡ Old.holeOut (Old.secondCell q)
computedRightHoleFluxAgreesWithOld Cell.q1 = refl
computedRightHoleFluxAgreesWithOld Cell.q3 = refl
computedRightHoleFluxAgreesWithOld Cell.q5 = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data ComputedAssemblyPhysicalLeaf : Set where
  PhysicalNodalCarrierSolve : ComputedAssemblyPhysicalLeaf
  PhysicalBernoulliWeights : ComputedAssemblyPhysicalLeaf
  SignedResidualCarrier : ComputedAssemblyPhysicalLeaf
  PhysicalGenerationRecombination : ComputedAssemblyPhysicalLeaf
  GeometricCellWeights : ComputedAssemblyPhysicalLeaf
  NonuniformMeshAssembly : ComputedAssemblyPhysicalLeaf
  SparseJacobianOfComputedFlux : ComputedAssemblyPhysicalLeaf
  PhysicalBoundaryConditions : ComputedAssemblyPhysicalLeaf

-- Firewalls:
-- computed finite face currents != calibrated SI Scharfetter-Gummel currents.
-- monus residuals require the admitted one-sided orientation and do not replace
-- a signed residual vector space.
-- agreement with the historical fixture validates reconstruction only; it does
-- not promote the historical fixture or the finite Bernoulli calibration.
