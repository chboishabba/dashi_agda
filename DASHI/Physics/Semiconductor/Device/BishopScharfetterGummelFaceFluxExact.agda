{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopScharfetterGummelFaceFluxExact where

------------------------------------------------------------------------
-- SIGNED BISHOP-REAL SCHARFETTER-GUMMEL FACE CORE
--
-- This owner consumes the Bishop-backed Bernoulli pair and forms the signed
-- exponential-fitting face balance on vendor/bishop's constructive real carrier:
--
--   J = u_L B(psi) - u_R B(-psi).
--
-- The dimensional q*D/dx or q*mu*V_T/dx prefactor is deliberately separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Physics.Semiconductor.Device.BishopBernoulliScharfetterGummelBridgeExact as Bernoulli
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as FiniteSG

record BishopFaceState
    (dataSet : Series.BishopElementaryPowerSeriesData) : Set where
  constructor bishopFaceState
  field
    leftPopulation : BishopReal.ℝ
    rightPopulation : BishopReal.ℝ
    weights : Bernoulli.BishopSGWeightPair dataSet

open BishopFaceState public

forwardContribution :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopFaceState dataSet → BishopReal.ℝ
forwardContribution face =
  BishopReal._*_
    (leftPopulation face)
    (Bernoulli.forwardWeight (weights face))

backwardContribution :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopFaceState dataSet → BishopReal.ℝ
backwardContribution face =
  BishopReal._*_
    (rightPopulation face)
    (Bernoulli.backwardWeight (weights face))

bishopSGFaceFlux :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopFaceState dataSet → BishopReal.ℝ
bishopSGFaceFlux face =
  BishopReal._-_
    (forwardContribution face)
    (backwardContribution face)

------------------------------------------------------------------------
-- Exact algebraic expansion receipt.
------------------------------------------------------------------------

bishopSGFaceFluxDefinition :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  (face : BishopFaceState dataSet) →
  BishopReal._≃_
    (bishopSGFaceFlux face)
    (BishopReal._-_
      (BishopReal._*_
        (leftPopulation face)
        (Bernoulli.forwardWeight (weights face)))
      (BishopReal._*_
        (rightPopulation face)
        (Bernoulli.backwardWeight (weights face))))
bishopSGFaceFluxDefinition face = BishopP.≃-refl

------------------------------------------------------------------------
-- Physical prefactor remains independent from the dimensionless SG balance.
------------------------------------------------------------------------

record BishopSGPhysicalPrefactor : Set where
  constructor bishopSGPhysicalPrefactor
  field
    chargeScale : BishopReal.ℝ
    diffusivityOrMobilityThermalScale : BishopReal.ℝ
    inverseMeshSpacing : BishopReal.ℝ
    faceMetric : BishopReal.ℝ

open BishopSGPhysicalPrefactor public

prefactorValue : BishopSGPhysicalPrefactor → BishopReal.ℝ
prefactorValue prefactor =
  BishopReal._*_
    (chargeScale prefactor)
    (BishopReal._*_
      (diffusivityOrMobilityThermalScale prefactor)
      (BishopReal._*_
        (inverseMeshSpacing prefactor)
        (faceMetric prefactor)))

physicalScaledFaceFlux :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopSGPhysicalPrefactor →
  BishopFaceState dataSet → BishopReal.ℝ
physicalScaledFaceFlux prefactor face =
  BishopReal._*_
    (prefactorValue prefactor)
    (bishopSGFaceFlux face)

------------------------------------------------------------------------
-- Promotion boundary from the historical finite Nat fixture.
--
-- A finite face flux is not identified with the Bishop signed flux by numeric
-- coincidence.  The caller must supply an embedding and a setoid equality.
------------------------------------------------------------------------

record FiniteFaceFluxMatchesBishop
    (dataSet : Series.BishopElementaryPowerSeriesData)
    (face : BishopFaceState dataSet) : Set₁ where
  field
    encodeFiniteFlux : Nat → BishopReal.ℝ
    finiteFluxCode : Nat
    finiteFluxMatches :
      BishopReal._≃_
        (encodeFiniteFlux finiteFluxCode)
        (bishopSGFaceFlux face)

open FiniteFaceFluxMatchesBishop public

record HistoricalFiniteFacePromotion
    (dataSet : Series.BishopElementaryPowerSeriesData)
    (face : BishopFaceState dataSet) : Set₁ where
  field
    sourceFace : FiniteSG.SGFace
    sourceCharge : Set
    agreement : FiniteFaceFluxMatchesBishop dataSet face

open HistoricalFiniteFacePromotion public

------------------------------------------------------------------------
-- Residual leaves.
------------------------------------------------------------------------

data BishopSGFluxResidualLeaf : Set where
  ConcreteBishopBernoulliPair : BishopSGFluxResidualLeaf
  PhysicalPotentialDrop : BishopSGFluxResidualLeaf
  PhysicalCarrierPopulations : BishopSGFluxResidualLeaf
  ChargeScaleCalibration : BishopSGFluxResidualLeaf
  MobilityOrDiffusivityCalibration : BishopSGFluxResidualLeaf
  ThermalVoltageCalibration : BishopSGFluxResidualLeaf
  MeshMetricCalibration : BishopSGFluxResidualLeaf
  FiniteToBishopFluxEqualityReceipt : BishopSGFluxResidualLeaf

-- Firewalls:
-- signed Bishop-real face balance != calibrated physical current density.
-- exact Bernoulli quotient != completed semiconductor constitutive model.
-- finite Nat flux != Bishop flux without FiniteFaceFluxMatchesBishop.
