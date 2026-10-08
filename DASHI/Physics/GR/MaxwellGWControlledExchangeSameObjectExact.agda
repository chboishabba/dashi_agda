module DASHI.Physics.GR.MaxwellGWControlledExchangeSameObjectExact where

open import DASHI.Core.Prelude

import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell
import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange

------------------------------------------------------------------------
-- MAXWELL x WEAK-FIELD GW SAME-OBJECT ADAPTER
--
-- The existing Maxwell adapter already supplies the literal potential A and
-- curvature F = dA while keeping metric/Hodge/source promotion fail-closed.
-- The existing GW law already supplies a literal perturbation and strain map.
-- This module makes those exact existing objects the inputs to the controlled
-- exchange lane.  The only new physical seam is the construction of the EM
-- stress tensor from that same Maxwell field on the chosen metric.
------------------------------------------------------------------------

record MaxwellLaserStressTarget : Set₁ where
  constructor maxwell-laser-stress-target
  field
    maxwell : Maxwell.MaxwellExteriorCalculusAdapter

    potential : Maxwell.OneForm
    curvature : Maxwell.TwoForm
    potentialIsCanonical :
      potential ≡ Maxwell.canonicalPotentialOneForm
    curvatureIsCanonical :
      curvature ≡ Maxwell.canonicalCurvatureTwoForm
    curvatureIsDOfPotential :
      Maxwell.d1 potential ≡ curvature

    EMStressEnergy : Set
    emStressEnergy : EMStressEnergy

    StressFromSameMaxwellFieldReceipt : Set
    stressFromSameMaxwellFieldReceipt : StressFromSameMaxwellFieldReceipt

open MaxwellLaserStressTarget public

canonicalMaxwellFieldTarget :
  (EMStressEnergy : Set) →
  (emStressEnergy : EMStressEnergy) →
  (StressFromSameMaxwellFieldReceipt : Set) →
  StressFromSameMaxwellFieldReceipt →
  MaxwellLaserStressTarget
canonicalMaxwellFieldTarget EMStressEnergy emStressEnergy
    StressFromSameMaxwellFieldReceipt receipt = record
  { maxwell = Maxwell.canonicalMaxwellExteriorCalculusAdapter
  ; potential = Maxwell.canonicalPotentialOneForm
  ; curvature = Maxwell.canonicalCurvatureTwoForm
  ; potentialIsCanonical = refl
  ; curvatureIsCanonical = refl
  ; curvatureIsDOfPotential = refl
  ; EMStressEnergy = EMStressEnergy
  ; emStressEnergy = emStressEnergy
  ; StressFromSameMaxwellFieldReceipt = StressFromSameMaxwellFieldReceipt
  ; stressFromSameMaxwellFieldReceipt = receipt
  }

record WeakFieldGWTarget
    (law : Laws.EinsteinGravityLaw)
    (wave : Laws.GravitationalWaveLaw law) : Set₁ where
  constructor weak-field-gw-target
  field
    background : Laws.GravitationalWaveLaw.BackgroundMetric wave
    perturbation : Laws.GravitationalWaveLaw.Perturbation wave
    waveEquation : Laws.GravitationalWaveLaw.WaveEquation wave
    waveEquationIsLinearisation :
      Laws.GravitationalWaveLaw.linearise wave background perturbation
        ≡ waveEquation
    weakFieldReceipt :
      Laws.GravitationalWaveLaw.weakFieldValid wave background perturbation

open WeakFieldGWTarget public

record MaxwellGWControlledExchangeWeld
    (law : Laws.EinsteinGravityLaw)
    (wave : Laws.GravitationalWaveLaw law) : Set₁ where
  constructor maxwell-gw-controlled-exchange-weld
  field
    laser : MaxwellLaserStressTarget
    gw : WeakFieldGWTarget law wave
    interaction : Exchange.EMGWInteractionCarrier

    MetricPerturbationSameObjectReceipt : Set
    metricPerturbationSameObjectReceipt : MetricPerturbationSameObjectReceipt

    EMStressSameObjectReceipt : Set
    emStressSameObjectReceipt : EMStressSameObjectReceipt

    MaxwellFieldSameObjectReceipt : Set
    maxwellFieldSameObjectReceipt : MaxwellFieldSameObjectReceipt

    WeakFieldSameObjectReceipt : Set
    weakFieldSameObjectReceipt : WeakFieldSameObjectReceipt

open MaxwellGWControlledExchangeWeld public

record MaxwellGWExchangeBoundary : Set where
  constructor maxwell-gw-exchange-boundary
  field
    canonicalMaxwellPotentialAndCurvatureReused : Bool
    canonicalGWWeakFieldPerturbationReused : Bool
    metricHodgeAuthorityStillRequiredForPhysicalEMStress : Bool
    sameObjectStressReceiptRequired : Bool
    sameObjectMetricPerturbationReceiptRequired : Bool
    controlledExchangeDoesNotPromoteFullMaxwellOrFullGR : Bool

canonicalMaxwellGWExchangeBoundary : MaxwellGWExchangeBoundary
canonicalMaxwellGWExchangeBoundary =
  maxwell-gw-exchange-boundary true true true true true true
