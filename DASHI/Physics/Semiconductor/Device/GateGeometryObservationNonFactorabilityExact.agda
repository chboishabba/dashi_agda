{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.GateGeometryObservationNonFactorabilityExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Geometry is an observer problem too.
--
-- A footprint/critical-dimension style projection can identify devices whose
-- gate-surrounding geometry differs.  The generic DASHI nonfactorability owner
-- then blocks reconstruction of an electrostatic-control observable from that
-- coarse footprint alone.
------------------------------------------------------------------------

data GateTopology : Set where
  planarLike finLike gateAllAroundLike : GateTopology

record GateGeometry : Set where
  constructor gateGeometry
  field
    topology            : GateTopology
    footprintWidthCode  : Nat
    channelThicknessCode : Nat
    surroundedFaceCode  : Nat
    electrostaticControlCode : Nat

open GateGeometry public

finGeometry : GateGeometry
finGeometry = gateGeometry finLike 20 6 3 70

nanosheetGeometry : GateGeometry
nanosheetGeometry = gateGeometry gateAllAroundLike 20 6 4 90

record CoarseGeometry : Set where
  constructor coarseGeometry
  field
    footprint : Nat
    thickness : Nat

open CoarseGeometry public

coarseGeometryProjection : GateGeometry → CoarseGeometry
coarseGeometryProjection x =
  coarseGeometry (footprintWidthCode x) (channelThicknessCode x)

controlObservable : GateGeometry → Nat
controlObservable = electrostaticControlCode

sameCoarseGeometry :
  coarseGeometryProjection finGeometry
  ≡ coarseGeometryProjection nanosheetGeometry
sameCoarseGeometry = refl

controlDiffers :
  controlObservable finGeometry ≡ controlObservable nanosheetGeometry → ⊥
controlDiffers ()

gateGeometryNonFactorability :
  NF.NonFactorabilityWitness coarseGeometryProjection controlObservable
gateGeometryNonFactorability =
  NF.nonFactorabilityWitness
    finGeometry nanosheetGeometry sameCoarseGeometry controlDiffers

coarseFootprintCannotDetermineControl :
  NF.FactorsThrough coarseGeometryProjection controlObservable → ⊥
coarseFootprintCannotDetermineControl =
  NF.witnessRulesOutEveryFlatFactorisation gateGeometryNonFactorability

------------------------------------------------------------------------
-- Physical residuals required before topology labels become a transistor model.
------------------------------------------------------------------------

data GeometryResidual : Set where
  GateOxideThickness       : GeometryResidual
  DielectricConstant       : GeometryResidual
  SheetWidthDistribution   : GeometryResidual
  SheetSpacing             : GeometryResidual
  FinHeight                : GeometryResidual
  CornerCurvature          : GeometryResidual
  WorkFunctionDistribution : GeometryResidual
  SourceDrainExtension     : GeometryResidual
  QuantumConfinement       : GeometryResidual
  PhysicalCapacitanceModel : GeometryResidual

-- Firewall:
-- topology label or coarse footprint != electrostatic-control theorem.
