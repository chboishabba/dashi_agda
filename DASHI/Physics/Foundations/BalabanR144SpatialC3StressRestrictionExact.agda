{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact where

------------------------------------------------------------------------
-- RESTRICT THE EXISTING CMP119/R144 B4 STRESS ACTION TO SPATIAL C3
--
-- The terminal R144 E1 theorem already uses the SAME hypercubic generator
-- family as the CMP109 source-covariance theorem.  For the Lorentzian stress
-- consumer, axis0 is time and axes1,2,3 are x,y,z.  Compose swap23 then swap12:
--
--   axis0 -> axis0
--   axis1 -> axis2
--   axis2 -> axis3
--   axis3 -> axis1
--
-- This is the physically aligned spatial C3 restriction.  No new ambient
-- recovery carrier is introduced here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyE1R144HypercubicReadoutMaxCutExact as R144E1
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

spatialXYZAxisImage : Signed.Axis4 → Signed.Axis4
spatialXYZAxisImage Signed.axis0 = Signed.axis0
spatialXYZAxisImage Signed.axis1 = Signed.axis2
spatialXYZAxisImage Signed.axis2 = Signed.axis3
spatialXYZAxisImage Signed.axis3 = Signed.axis1

spatialXYZAxisAction : Signed.SignedAxisAction
spatialXYZAxisAction = record
  { Signed.SignedAxisAction.axisImage = spatialXYZAxisImage
  ; Signed.SignedAxisAction.axisSign = λ _ → Signed.plus
  }

-- The direct action is definitionally the composition of the two existing B4
-- generators used by the source-backed spatial 123 cycle.
spatialXYZAxisActionMatchesB4Composition : ∀ axis →
  Signed.axisImage spatialXYZAxisAction axis
  ≡ Signed.axisImage (Axis.hypercubicSignedAxisAction Hyper.swap12)
      (Signed.axisImage (Axis.hypercubicSignedAxisAction Hyper.swap23) axis)
spatialXYZAxisActionMatchesB4Composition Signed.axis0 = refl
spatialXYZAxisActionMatchesB4Composition Signed.axis1 = refl
spatialXYZAxisActionMatchesB4Composition Signed.axis2 = refl
spatialXYZAxisActionMatchesB4Composition Signed.axis3 = refl

spatialXYZComponent :
  K.SymmetricTensorComponent4 → K.SymmetricTensorComponent4
spatialXYZComponent component =
  Signed.component (Signed.actSignedComponent spatialXYZAxisAction component)

spatialXYZComponentCubed : ∀ component →
  spatialXYZComponent
    (spatialXYZComponent (spatialXYZComponent component)) ≡ component
spatialXYZComponentCubed K.component00 = refl
spatialXYZComponentCubed K.component01 = refl
spatialXYZComponentCubed K.component02 = refl
spatialXYZComponentCubed K.component03 = refl
spatialXYZComponentCubed K.component11 = refl
spatialXYZComponentCubed K.component12 = refl
spatialXYZComponentCubed K.component13 = refl
spatialXYZComponentCubed K.component22 = refl
spatialXYZComponentCubed K.component23 = refl
spatialXYZComponentCubed K.component33 = refl

r144SpatialTensorC3Action : C3.OrderThreeAction K.SymmetricTensorComponent4
r144SpatialTensorC3Action = record
  { C3.OrderThreeAction.rotate = spatialXYZComponent
  ; C3.OrderThreeAction.rotateCubed = spatialXYZComponentCubed
  }

-- Sanity checks: time is fixed and the spatial stress slots rotate cyclically.
cycleKeeps00 : spatialXYZComponent K.component00 ≡ K.component00
cycleKeeps00 = refl

cycle01To02 : spatialXYZComponent K.component01 ≡ K.component02
cycle01To02 = refl

cycle02To03 : spatialXYZComponent K.component02 ≡ K.component03
cycle02To03 = refl

cycle03To01 : spatialXYZComponent K.component03 ≡ K.component01
cycle03To01 = refl

cycle11To22 : spatialXYZComponent K.component11 ≡ K.component22
cycle11To22 = refl

cycle22To33 : spatialXYZComponent K.component22 ≡ K.component33
cycle22To33 = refl

cycle33To11 : spatialXYZComponent K.component33 ≡ K.component11
cycle33To11 = refl

cycle12To23 : spatialXYZComponent K.component12 ≡ K.component23
cycle12To23 = refl

cycle23To13 : spatialXYZComponent K.component23 ≡ K.component13
cycle23To13 = refl

cycle13To12 : spatialXYZComponent K.component13 ≡ K.component12
cycle13To12 = refl

------------------------------------------------------------------------
-- Frontier accounting.
--
-- R144E1.R144HypercubicSignedReadoutCovariance already states covariance of
-- the actual finite-D1 readout under every generator in this B4 family.  The
-- spatial C3 uses only swap23 and swap12 from that same family.  Consequently
-- no new ambient carrier or independent stress action is needed: physical
-- source->stress C3 is the restriction/composition of that existing terminal
-- covariance witness.
------------------------------------------------------------------------

r144C3RestrictedFromExistingB4Action : Bool
r144C3RestrictedFromExistingB4Action = true

r144SpatialC3TensorActionRecovered : Bool
r144SpatialC3TensorActionRecovered = true

r144SpatialC3NeedsNoNewAmbientCarrier : Bool
r144SpatialC3NeedsNoNewAmbientCarrier = true

r144PhysicalReadoutC3DependsOnExistingTerminalCovarianceWitness : Bool
r144PhysicalReadoutC3DependsOnExistingTerminalCovarianceWitness = true

r144TerminalCovarianceAlreadyNamesSameWholeLatticeAction : Bool
r144TerminalCovarianceAlreadyNamesSameWholeLatticeAction = true

record BalabanR144SpatialC3Boundary : Set where
  constructor balaban-r144-spatial-c3-boundary
  field
    spatial123FixesTime : Bool
    tensorSlotOrderThreeActionConstructed : Bool
    sameHypercubicGeneratorFamilyReused : Bool
    newAmbientRecoveryCarrierRequired : Bool
    terminalR144CovarianceWitnessRemainsPhysicalPayment : Bool

canonicalBalabanR144SpatialC3Boundary : BalabanR144SpatialC3Boundary
canonicalBalabanR144SpatialC3Boundary =
  balaban-r144-spatial-c3-boundary true true true false true
