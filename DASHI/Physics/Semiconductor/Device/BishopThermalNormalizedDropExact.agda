{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopThermalNormalizedDropExact where

------------------------------------------------------------------------
-- SAME-OBJECT THERMAL NORMALIZATION OF THE FINITE DEVICE POTENTIAL DROP
--
-- The finite SG fixture already computes every nodal potential from the same
-- source-charge state.  Each admitted face has one potential-code step.
--
-- This owner introduces a deliberately finite thermal-voltage calibration:
-- two potential-code units per thermal-voltage unit.  The corresponding
-- Bishop-real dimensionless drop is therefore 1/2, characterized by the exact
-- cross-multiplied law
--
--     psi * V_T  ~=  Delta phi.
--
-- This is a calibration fixture, NOT yet the physical law V_T = k_B T / q.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_∸_)
open import Data.Rational.Unnormalised using (1ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as UnitBase
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as FiniteSG

------------------------------------------------------------------------
-- The face drop is computed from the same nodal-potential producer.
------------------------------------------------------------------------

facePotentialDropCode : Cell.SourceCharge → FiniteSG.SGFace → Nat
facePotentialDropCode q face =
  FiniteSG.nodePotential q (FiniteSG.rightNode face)
  ∸ FiniteSG.nodePotential q (FiniteSG.leftNode face)

facePotentialDropIsOne :
  (q : Cell.SourceCharge) →
  (face : FiniteSG.SGFace) →
  facePotentialDropCode q face ≡ 1
facePotentialDropIsOne Cell.q1 FiniteSG.face01 = refl
facePotentialDropIsOne Cell.q1 FiniteSG.face12 = refl
facePotentialDropIsOne Cell.q1 FiniteSG.face23 = refl
facePotentialDropIsOne Cell.q3 FiniteSG.face01 = refl
facePotentialDropIsOne Cell.q3 FiniteSG.face12 = refl
facePotentialDropIsOne Cell.q3 FiniteSG.face23 = refl
facePotentialDropIsOne Cell.q5 FiniteSG.face01 = refl
facePotentialDropIsOne Cell.q5 FiniteSG.face12 = refl
facePotentialDropIsOne Cell.q5 FiniteSG.face23 = refl

------------------------------------------------------------------------
-- Finite thermal calibration on the Bishop carrier.
------------------------------------------------------------------------

embedCode : Nat → BishopReal.ℝ
embedCode n = BishopReal._⋆ (+ n / 1)

thermalVoltageCode : Nat
thermalVoltageCode = 2

thermalVoltage : BishopReal.ℝ
thermalVoltage = embedCode thermalVoltageCode

normalizedDrop : BishopReal.ℝ
normalizedDrop = Exp.half

potentialDrop : Cell.SourceCharge → FiniteSG.SGFace → BishopReal.ℝ
potentialDrop q face = embedCode (facePotentialDropCode q face)

unitThermalNormalization :
  BishopReal._≃_
    (BishopReal._*_ normalizedDrop thermalVoltage)
    (embedCode 1)
unitThermalNormalization =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ (+ 1 / 2) ⊗ Κ (+ 2 / 1)) ⊜ Κ (+ 1 / 1))
    BishopP.≃-refl

thermalNormalization :
  (q : Cell.SourceCharge) →
  (face : FiniteSG.SGFace) →
  BishopReal._≃_
    (BishopReal._*_ normalizedDrop thermalVoltage)
    (potentialDrop q face)
thermalNormalization q face
  rewrite facePotentialDropIsOne q face =
  unitThermalNormalization

------------------------------------------------------------------------
-- The calibrated drop inhabits the concrete Bernoulli chart.
------------------------------------------------------------------------

normalizedDropNonnegative : BishopReal.NonNegative normalizedDrop
normalizedDropNonnegative =
  BishopP.pos⇒nonNeg (BishopP.0<x⇒posx Exp.halfPositive)

normalizedDropBelowOrEqualOne :
  BishopReal._≤_ normalizedDrop BishopReal.1ℝ
normalizedDropBelowOrEqualOne = BishopP.<⇒≤ Exp.halfBelowOne

normalizedDropUnitPoint : UnitBase.UnitIntervalPoint normalizedDrop
normalizedDropUnitPoint = record
  { nonnegative = normalizedDropNonnegative
  ; belowOne = normalizedDropBelowOrEqualOne
  }

normalizedDropPositiveUnitPoint : Unit.PositiveUnitIntervalPoint normalizedDrop
normalizedDropPositiveUnitPoint = record
  { unitPoint = normalizedDropUnitPoint
  ; positive = Exp.halfPositive
  }

record SameObjectThermalDrop
    (q : Cell.SourceCharge)
    (face : FiniteSG.SGFace) : Set where
  constructor sameObjectThermalDrop
  field
    finiteDropIsOne : facePotentialDropCode q face ≡ 1
    crossMultipliedNormalization :
      BishopReal._≃_
        (BishopReal._*_ normalizedDrop thermalVoltage)
        (potentialDrop q face)
    chartReceipt : Unit.PositiveUnitIntervalPoint normalizedDrop

open SameObjectThermalDrop public

sameObjectThermalDropReceipt :
  (q : Cell.SourceCharge) →
  (face : FiniteSG.SGFace) →
  SameObjectThermalDrop q face
sameObjectThermalDropReceipt q face = record
  { finiteDropIsOne = facePotentialDropIsOne q face
  ; crossMultipliedNormalization = thermalNormalization q face
  ; chartReceipt = normalizedDropPositiveUnitPoint
  }

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data ThermalDropResidualLeaf : Set where
  PhysicalKelvinTemperature : ThermalDropResidualLeaf
  BoltzmannConstantCalibration : ThermalDropResidualLeaf
  ElementaryChargeCalibration : ThermalDropResidualLeaf
  PhysicalThermalVoltageLaw : ThermalDropResidualLeaf
  PotentialCodeToVoltCalibration : ThermalDropResidualLeaf
  PhysicalPotentialDrop : ThermalDropResidualLeaf
  GlobalDropChartCoverage : ThermalDropResidualLeaf

-- Firewalls:
-- thermalVoltageCode = 2 is a finite calibration, not a claim that V_T=2 volts.
-- normalizedDrop = 1/2 is dimensionless and local to this admitted fixture.
-- psi*V_T ~= Delta-phi does not itself prove V_T = k_B*T/q.
-- positive-unit-interval membership on the finite mesh is not a global device
-- potential theorem.
