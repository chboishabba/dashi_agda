module DASHI.Physics.GR.ControlledEMGWEnergyFrequencyPhaseCalibrationExact where

open import DASHI.Core.Prelude

import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant
import DASHI.Constants.Registry as Registry
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange

------------------------------------------------------------------------
-- CONTROLLED EM-GW ENERGY -> FREQUENCY -> PHASE CALIBRATION
--
-- Reuse the existing repo SI/spectroscopy authority surface.  In particular,
-- the repository already records the exact Planck constant slot and the
-- symbolic laws Delta E = h nu = hbar omega.  This module does not invent a
-- second constants table; it makes those exact existing slots consumers of the
-- controlled exchange readout.
------------------------------------------------------------------------

existingSpectroscopyAdapter : Quant.SpectroscopyObservableAdapter
existingSpectroscopyAdapter = Quant.canonicalSpectroscopyObservableAdapter

record EnergyFrequencyPhaseCalibration
    (interaction : Exchange.EMGWInteractionCarrier) : Set₁ where
  constructor energy-frequency-phase-calibration
  field
    registry : Registry.ConstantsRegistry
    spectroscopy : Quant.SpectroscopyObservableAdapter

    spectroscopyIsCanonical :
      spectroscopy ≡ Quant.canonicalSpectroscopyObservableAdapter

    ExchangeEnergy : Set
    exchangeEnergy : ExchangeEnergy

    OpticalAngularFrequencyShift : Set
    opticalAngularFrequencyShift : OpticalAngularFrequencyShift

    DelayTime : Set
    delayTime : DelayTime

    DelayedPhaseShift : Set
    delayedPhaseShift : DelayedPhaseShift

    SameWorkEnergyReceipt : Set
    sameWorkEnergyReceipt : SameWorkEnergyReceipt

    PlanckEnergyFrequencyReceipt : Set
    planckEnergyFrequencyReceipt : PlanckEnergyFrequencyReceipt

    AngularFrequencyConventionReceipt : Set
    angularFrequencyConventionReceipt : AngularFrequencyConventionReceipt

    PhaseAccumulationReceipt : Set
    phaseAccumulationReceipt : PhaseAccumulationReceipt

    SameInteractionFrequencyReceipt : Set
    sameInteractionFrequencyReceipt : SameInteractionFrequencyReceipt

    SameInteractionPhaseReceipt : Set
    sameInteractionPhaseReceipt : SameInteractionPhaseReceipt

open EnergyFrequencyPhaseCalibration public

------------------------------------------------------------------------
-- The repo authority surface already names all needed symbolic relations.
------------------------------------------------------------------------

existingPlanckSlotLabel : String
existingPlanckSlotLabel =
  Quant.SpectroscopyObservableAdapter.hSlotLabel existingSpectroscopyAdapter

existingHbarSlotLabel : String
existingHbarSlotLabel =
  Quant.SpectroscopyObservableAdapter.hbarSlotLabel existingSpectroscopyAdapter

existingEnergyFrequencyLaw : String
existingEnergyFrequencyLaw =
  Quant.SpectroscopyObservableAdapter.hFrequencyExpression existingSpectroscopyAdapter

existingAngularEnergyLaw : String
existingAngularEnergyLaw =
  Quant.SpectroscopyObservableAdapter.hbarAngularFrequencyExpression existingSpectroscopyAdapter

record EnergyFrequencyPhaseBoundary : Set where
  constructor energy-frequency-phase-boundary
  field
    exactSIRegistryAlreadyExists : Bool
    planckConstantSlotAlreadyExists : Bool
    hbarSlotAlreadyExists : Bool
    energyFrequencyLawAlreadyExists : Bool
    angularEnergyLawAlreadyExists : Bool
    duplicateConstantsAdapterNeeded : Bool
    experimentSpecificWorkEnergyWeldStillRequired : Bool
    experimentSpecificDelayPhaseCalibrationStillRequired : Bool

canonicalEnergyFrequencyPhaseBoundary : EnergyFrequencyPhaseBoundary
canonicalEnergyFrequencyPhaseBoundary =
  energy-frequency-phase-boundary
    true true true true true false true true
