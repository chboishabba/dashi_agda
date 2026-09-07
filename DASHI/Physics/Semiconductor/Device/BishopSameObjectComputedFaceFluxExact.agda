{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopSameObjectComputedFaceFluxExact where

------------------------------------------------------------------------
-- SAME-OBJECT COMPUTED BISHOP SG FACE FLUX
--
-- This owner removes the remaining abstract drop input from the preferred
-- Bishop SG path.  The drop comes from BishopThermalNormalizedDropExact, which
-- in turn consumes the actual finite nodal-potential producer.  Carrier
-- populations are the existing finite nodal populations embedded into the
-- Bishop real carrier.
--
-- The embedding remains a synthetic finite population calibration.  It is NOT
-- yet a physical density in m^-3.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as FiniteSG
import DASHI.Physics.Semiconductor.Device.BishopThermalNormalizedDropExact as Thermal
import DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact as BishopSG

------------------------------------------------------------------------
-- Finite carrier populations embedded on the canonical Bishop real carrier.
------------------------------------------------------------------------

embedPopulationCode : Nat → BishopReal.ℝ
embedPopulationCode n = BishopReal._⋆ (+ n / 1)

electronLeftPopulation :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
electronLeftPopulation q face =
  embedPopulationCode
    (FiniteSG.electronPopulationAt q (FiniteSG.leftNode face))

electronRightPopulation :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
electronRightPopulation q face =
  embedPopulationCode
    (FiniteSG.electronPopulationAt q (FiniteSG.rightNode face))

holeLeftPopulation :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
holeLeftPopulation q face =
  embedPopulationCode
    (FiniteSG.holePopulationAt q (FiniteSG.leftNode face))

holeRightPopulation :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
holeRightPopulation q face =
  embedPopulationCode
    (FiniteSG.holePopulationAt q (FiniteSG.rightNode face))

------------------------------------------------------------------------
-- The concrete face constructors now take no arbitrary drop or Bernoulli data.
------------------------------------------------------------------------

electronFaceState :
  Cell.SourceCharge → FiniteSG.SGFace → BishopSG.ConcreteBishopFaceState
electronFaceState q face = record
  { leftPopulation = electronLeftPopulation q face
  ; rightPopulation = electronRightPopulation q face
  ; drop = Thermal.normalizedDrop
  ; dropInPositiveUnitInterval =
      Thermal.chartReceipt (Thermal.sameObjectThermalDropReceipt q face)
  }

holeFaceState :
  Cell.SourceCharge → FiniteSG.SGFace → BishopSG.ConcreteBishopFaceState
holeFaceState q face = record
  { leftPopulation = holeLeftPopulation q face
  ; rightPopulation = holeRightPopulation q face
  ; drop = Thermal.normalizedDrop
  ; dropInPositiveUnitInterval =
      Thermal.chartReceipt (Thermal.sameObjectThermalDropReceipt q face)
  }

bishopElectronFaceFlux :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
bishopElectronFaceFlux q face =
  BishopSG.concreteBishopSGFaceFlux (electronFaceState q face)

bishopHoleFaceFlux :
  Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
bishopHoleFaceFlux q face =
  BishopSG.concreteBishopSGFaceFlux (holeFaceState q face)

------------------------------------------------------------------------
-- Dependency receipts: the drop on each face is the same normalized drop whose
-- cross-multiplied law is tied to the actual finite nodal potential difference.
------------------------------------------------------------------------

electronFaceThermalNormalization = Thermal.thermalNormalization
holeFaceThermalNormalization = Thermal.thermalNormalization

------------------------------------------------------------------------
-- Same internal face is consumed by both neighbouring control volumes.
-- No second face-current value exists to be reconciled.
------------------------------------------------------------------------

internalElectronFace : Cell.SourceCharge → BishopReal.ℝ
internalElectronFace q = bishopElectronFaceFlux q FiniteSG.face12

internalHoleFace : Cell.SourceCharge → BishopReal.ℝ
internalHoleFace q = bishopHoleFaceFlux q FiniteSG.face12

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data SameObjectBishopFluxResidualLeaf : Set where
  PhysicalCarrierDensityEmbedding : SameObjectBishopFluxResidualLeaf
  PhysicalThermalVoltage : SameObjectBishopFluxResidualLeaf
  MobilityOrDiffusivityCalibration : SameObjectBishopFluxResidualLeaf
  MeshSpacingCalibration : SameObjectBishopFluxResidualLeaf
  FaceMetricCalibration : SameObjectBishopFluxResidualLeaf
  ChargeScaleCalibration : SameObjectBishopFluxResidualLeaf
  BishopContinuityResidualAssembly : SameObjectBishopFluxResidualLeaf
  SparseFluxJacobian : SameObjectBishopFluxResidualLeaf

-- Firewalls:
-- embedding finite population codes into Bishop reals != physical carrier
-- density calibration.
-- same-object Bishop SG face balance != SI current density until dimensional
-- transport and geometry prefactors are supplied.
-- the finite thermal chart != a proof of the physical k_B*T/q law.
