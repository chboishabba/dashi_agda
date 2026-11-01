{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact where

------------------------------------------------------------------------
-- CONCRETE BISHOP SG FACE FLUX
--
-- The Bernoulli weights are no longer arbitrary inputs.  A positive
-- unit-interval dimensionless drop determines both B(+psi) and B(-psi)
-- constructively through the concrete Bishop exponential and inverse owners.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Physics.Semiconductor.Device.BishopConcreteBernoulliPairExact as Bernoulli

record ConcreteBishopFaceState : Set₁ where
  constructor concreteBishopFaceState
  field
    leftPopulation : BishopReal.ℝ
    rightPopulation : BishopReal.ℝ
    drop : BishopReal.ℝ
    dropInPositiveUnitInterval : Unit.PositiveUnitIntervalPoint drop

open ConcreteBishopFaceState public

forwardContribution : ConcreteBishopFaceState → BishopReal.ℝ
forwardContribution face =
  BishopReal._*_
    (leftPopulation face)
    (Bernoulli.forwardWeight (dropInPositiveUnitInterval face))

backwardContribution : ConcreteBishopFaceState → BishopReal.ℝ
backwardContribution face =
  BishopReal._*_
    (rightPopulation face)
    (Bernoulli.backwardWeight (dropInPositiveUnitInterval face))

concreteBishopSGFaceFlux : ConcreteBishopFaceState → BishopReal.ℝ
concreteBishopSGFaceFlux face =
  BishopReal._-_
    (forwardContribution face)
    (backwardContribution face)

concreteBishopSGFaceFluxDefinition :
  (face : ConcreteBishopFaceState) →
  BishopReal._≃_
    (concreteBishopSGFaceFlux face)
    (BishopReal._-_
      (BishopReal._*_
        (leftPopulation face)
        (Bernoulli.forwardWeight (dropInPositiveUnitInterval face)))
      (BishopReal._*_
        (rightPopulation face)
        (Bernoulli.backwardWeight (dropInPositiveUnitInterval face))))
concreteBishopSGFaceFluxDefinition face = BishopP.≃-refl

------------------------------------------------------------------------
-- Physical scaling remains an independent producer.
------------------------------------------------------------------------

record ConcreteBishopSGPhysicalPrefactor : Set where
  constructor concreteBishopSGPhysicalPrefactor
  field
    chargeScale : BishopReal.ℝ
    transportThermalScale : BishopReal.ℝ
    inverseMeshSpacing : BishopReal.ℝ
    faceMetric : BishopReal.ℝ

open ConcreteBishopSGPhysicalPrefactor public

prefactorValue : ConcreteBishopSGPhysicalPrefactor → BishopReal.ℝ
prefactorValue prefactor =
  BishopReal._*_
    (chargeScale prefactor)
    (BishopReal._*_
      (transportThermalScale prefactor)
      (BishopReal._*_
        (inverseMeshSpacing prefactor)
        (faceMetric prefactor)))

physicalScaledConcreteFaceFlux :
  ConcreteBishopSGPhysicalPrefactor →
  ConcreteBishopFaceState →
  BishopReal.ℝ
physicalScaledConcreteFaceFlux prefactor face =
  BishopReal._*_
    (prefactorValue prefactor)
    (concreteBishopSGFaceFlux face)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data ConcreteBishopSGResidualLeaf : Set where
  PhysicalDimensionlessPotentialDrop : ConcreteBishopSGResidualLeaf
  PhysicalCarrierPopulationLeft : ConcreteBishopSGResidualLeaf
  PhysicalCarrierPopulationRight : ConcreteBishopSGResidualLeaf
  ChargeScaleCalibration : ConcreteBishopSGResidualLeaf
  MobilityDiffusivityThermalScale : ConcreteBishopSGResidualLeaf
  MeshSpacingCalibration : ConcreteBishopSGResidualLeaf
  FaceMetricCalibration : ConcreteBishopSGResidualLeaf
  SparseFluxJacobian : ConcreteBishopSGResidualLeaf

-- Firewalls:
-- a constructive dimensionless Bishop flux is not yet SI current density.
-- positive-unit-interval drop is a local chart restriction, not a global device
-- potential theorem.
-- exact Bernoulli construction does not supply carrier populations, geometry,
-- mobility/diffusivity, thermal voltage, or contact boundary data.
