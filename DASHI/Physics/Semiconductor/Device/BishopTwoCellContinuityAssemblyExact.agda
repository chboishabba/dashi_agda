{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopTwoCellContinuityAssemblyExact where

------------------------------------------------------------------------
-- SIGNED BISHOP-REAL TWO-CELL CONTINUITY ASSEMBLY
--
-- This is the analytic counterpart of the finite Nat-monus residual owner.
-- Face currents come from BishopSameObjectComputedFaceFluxExact, so the active
-- path is now
--
--   computed nodal state -> thermal-normalized drop -> Bishop Bernoulli weights
--   -> signed SG face flux -> signed local continuity residual.
--
-- No claim is made that these residuals equal the historical finite scores
-- 6,3,0.  Those scores depended on the old finite (2,1) calibration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as FiniteSG
import DASHI.Physics.Semiconductor.Device.ComputedFluxTwoCellContinuityExact as FiniteAssembly
import DASHI.Physics.Semiconductor.Device.BishopSameObjectComputedFaceFluxExact as BishopFlux

embedCode : Nat → BishopReal.ℝ
embedCode n = BishopReal._⋆ (+ n / 1)

------------------------------------------------------------------------
-- Existing generation/recombination codes embedded on the Bishop carrier.
------------------------------------------------------------------------

generationA : Cell.SourceCharge → BishopReal.ℝ
generationA q = embedCode (FiniteAssembly.generationA q)

recombinationA : Cell.SourceCharge → BishopReal.ℝ
recombinationA q = embedCode (FiniteAssembly.recombinationA q)

generationB : Cell.SourceCharge → BishopReal.ℝ
generationB q = embedCode (FiniteAssembly.generationB q)

recombinationB : Cell.SourceCharge → BishopReal.ℝ
recombinationB q = embedCode (FiniteAssembly.recombinationB q)

------------------------------------------------------------------------
-- Signed local residuals.
--
-- Electron residual:  Jin + G - Jout - R.
-- Hole residual:      Jout + R - Jin - G.
--
-- These are genuine signed Bishop reals; there is no monus/orientation loss.
------------------------------------------------------------------------

electronResidualA : Cell.SourceCharge → BishopReal.ℝ
electronResidualA q =
  BishopReal._-_
    (BishopReal._+_
      (BishopFlux.bishopElectronFaceFlux q FiniteSG.face01)
      (generationA q))
    (BishopReal._+_
      (BishopFlux.bishopElectronFaceFlux q FiniteSG.face12)
      (recombinationA q))

holeResidualA : Cell.SourceCharge → BishopReal.ℝ
holeResidualA q =
  BishopReal._-_
    (BishopReal._+_
      (BishopFlux.bishopHoleFaceFlux q FiniteSG.face12)
      (recombinationA q))
    (BishopReal._+_
      (BishopFlux.bishopHoleFaceFlux q FiniteSG.face01)
      (generationA q))

electronResidualB : Cell.SourceCharge → BishopReal.ℝ
electronResidualB q =
  BishopReal._-_
    (BishopReal._+_
      (BishopFlux.bishopElectronFaceFlux q FiniteSG.face12)
      (generationB q))
    (BishopReal._+_
      (BishopFlux.bishopElectronFaceFlux q FiniteSG.face23)
      (recombinationB q))

holeResidualB : Cell.SourceCharge → BishopReal.ℝ
holeResidualB q =
  BishopReal._-_
    (BishopReal._+_
      (BishopFlux.bishopHoleFaceFlux q FiniteSG.face23)
      (recombinationB q))
    (BishopReal._+_
      (BishopFlux.bishopHoleFaceFlux q FiniteSG.face12)
      (generationB q))

------------------------------------------------------------------------
-- Same-object internal face ownership is definitional: both cell residuals
-- consume exactly the same face12 flux producer.
------------------------------------------------------------------------

sharedElectronInternalFace : Cell.SourceCharge → BishopReal.ℝ
sharedElectronInternalFace = BishopFlux.internalElectronFace

sharedHoleInternalFace : Cell.SourceCharge → BishopReal.ℝ
sharedHoleInternalFace = BishopFlux.internalHoleFace

------------------------------------------------------------------------
-- Closure is componentwise and setoid-aware.  No closure inhabitant is asserted
-- until the physical/calibrated residual equations are actually proved.
------------------------------------------------------------------------

record BishopContinuityClosed (q : Cell.SourceCharge) : Set where
  field
    electronAZero : BishopReal._≃_ (electronResidualA q) BishopReal.0ℝ
    holeAZero : BishopReal._≃_ (holeResidualA q) BishopReal.0ℝ
    electronBZero : BishopReal._≃_ (electronResidualB q) BishopReal.0ℝ
    holeBZero : BishopReal._≃_ (holeResidualB q) BishopReal.0ℝ

open BishopContinuityClosed public

------------------------------------------------------------------------
-- Regression firewall.
------------------------------------------------------------------------

data BishopAssemblyRegressionBoundary : Set where
  FiniteScoreDoesNotIdentifyBishopResidual : BishopAssemblyRegressionBoundary
  FiniteClosureDoesNotIdentifyBishopClosure : BishopAssemblyRegressionBoundary

------------------------------------------------------------------------
-- Remaining physical leaves.
------------------------------------------------------------------------

data BishopAssemblyResidualLeaf : Set where
  PhysicalCarrierDensityCalibration : BishopAssemblyResidualLeaf
  PhysicalGenerationRecombination : BishopAssemblyResidualLeaf
  PhysicalThermalVoltageLaw : BishopAssemblyResidualLeaf
  DimensionalCurrentPrefactor : BishopAssemblyResidualLeaf
  CellVolumeAndFaceAreaMetrics : BishopAssemblyResidualLeaf
  ContactBoundaryConditions : BishopAssemblyResidualLeaf
  SparseFluxJacobian : BishopAssemblyResidualLeaf
  ResidualNorm : BishopAssemblyResidualLeaf
  DampedUpdateLaw : BishopAssemblyResidualLeaf
  BasinPreservation : BishopAssemblyResidualLeaf

-- Firewalls:
-- finite residual score agreement is intentionally absent here.
-- a signed Bishop residual vector != a physical SI residual until current,
-- source, and geometry units are calibrated.
-- symbolic continuity assembly != convergence of Newton/Gummel iteration.
