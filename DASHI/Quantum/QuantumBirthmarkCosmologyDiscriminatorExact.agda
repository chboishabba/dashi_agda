{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkCosmologyDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.GRQFTExperimentDesignCrossPollinationExact as Experiment
import DASHI.Quantum.QuantumBirthmarkHistorySectorDarkEnergyExact as History

------------------------------------------------------------------------
-- FALSIFIABLE DISCRIMINATORS FOR THE HISTORY-SECTOR DARK-ENERGY HYPOTHESIS
--
-- These are experiment-design coordinates, not established predictions.  The
-- point is to make the proposal lose against LCDM / generic evolving-w models
-- if the required correlations are absent.
------------------------------------------------------------------------

data HistoryDarkEnergyDiscriminator : Set where
  evolvingEquationOfStateDiscriminator : HistoryDarkEnergyDiscriminator
  structureHistoryCorrelationDiscriminator : HistoryDarkEnergyDiscriminator
  entropyProductionCorrelationDiscriminator : HistoryDarkEnergyDiscriminator
  laboratoryResidualBackreactionDiscriminator : HistoryDarkEnergyDiscriminator
  regularCorePopulationDiscriminator : HistoryDarkEnergyDiscriminator

record CosmologyDiscriminatorTarget : Set where
  constructor cosmology-discriminator-target
  field
    target : HistoryDarkEnergyDiscriminator
    observableReference : String
    nullReference : String
    nuisanceReference : String
    positiveSignalUniquelyIdentifiesHistorySector : Bool

open CosmologyDiscriminatorTarget public

wzTarget : CosmologyDiscriminatorTarget
wzTarget =
  cosmology-discriminator-target
    evolvingEquationOfStateDiscriminator
    "Reconstruct w(z), including w0-wa descriptions, from expansion and growth data"
    "w=-1 remains an allowed null; generic evolving-w alternatives must also be compared"
    "distance calibration, growth modelling, neutrino mass, curvature, survey systematics"
    false

structureHistoryTarget : CosmologyDiscriminatorTarget
structureHistoryTarget =
  cosmology-discriminator-target
    structureHistoryCorrelationDiscriminator
    "Test whether inferred dark-energy evolution tracks independently reconstructed structure/entropy-history proxies"
    "No correlation after conditioning on standard cosmological parameters"
    "proxy definition, baryonic feedback, selection effects, look-elsewhere freedom"
    false

laboratoryBackreactionTarget : CosmologyDiscriminatorTarget
laboratoryBackreactionTarget =
  cosmology-discriminator-target
    laboratoryResidualBackreactionDiscriminator
    "Compare gravitational observables across controlled quantum-history/decoherence protocols at matched ordinary stress-energy"
    "No extra metric/gravitational signal beyond standard semiclassical/systematic expectations"
    "electromagnetic, thermal, vibration, Casimir, mass-motion and readout backaction"
    false

------------------------------------------------------------------------
-- Current observational status boundary, 2026-10-13.
------------------------------------------------------------------------

DESIDR2MixedEvidenceRecorded : Bool
DESIDR2MixedEvidenceRecorded = true

DESIEvolvingDarkEnergyEstablished : Bool
DESIEvolvingDarkEnergyEstablished = false

RomanLaunched20260830Recorded : Bool
RomanLaunched20260830Recorded = true

RomanDarkEnergyConstraintAvailableAtLaunch : Bool
RomanDarkEnergyConstraintAvailableAtLaunch = false

EuclidProvidesRelevantDarkEnergySurveyChannel : Bool
EuclidProvidesRelevantDarkEnergySurveyChannel = true

positiveSignalDoesNotUniquelyIdentifyHistorySector : Bool
positiveSignalDoesNotUniquelyIdentifyHistorySector = true

nullWEqualsMinusOneWouldStronglyConstrainSimpleHistoryScaling : Bool
nullWEqualsMinusOneWouldStronglyConstrainSimpleHistoryScaling = true

------------------------------------------------------------------------
-- Specific theory-discriminating predictions that require a model mapping.
------------------------------------------------------------------------

record HistoryScalingPrediction : Set₁ where
  field
    CosmicTime : Set
    HistoryProxy : CosmicTime → Set
    DarkEnergyObservable : CosmicTime → Set

    historyToDarkEnergyPrediction :
      (t : CosmicTime) → HistoryProxy t → DarkEnergyObservable t

    -- A concrete model must provide this map before "lockstep with entropy
    -- production" becomes a prediction rather than a narrative.
    quantitativeScalingLawDerived : Bool

open HistoryScalingPrediction public

wzFromHistoryAccumulationDerived : Bool
wzFromHistoryAccumulationDerived = false

coincidenceRatioFromHistoryAccumulationDerived : Bool
coincidenceRatioFromHistoryAccumulationDerived = false

labResidualBackreactionMagnitudeDerived : Bool
labResidualBackreactionMagnitudeDerived = false

------------------------------------------------------------------------
-- Source notes.
------------------------------------------------------------------------

desi2026Status : String
desi2026Status =
  "DESI DR2 remains a discriminator for evolving dark energy; the 2026 Ly-alpha full-shape result shifted toward LambdaCDM, so evolving dark energy is not treated as established"

roman2026Status : String
roman2026Status =
  "NASA Roman launched 2026-08-30 and is a future/commissioning-era dark-energy constraint channel, not an existing confirmation of the history-sector hypothesis"

experimentDesignReuse : Bool
experimentDesignReuse = true
