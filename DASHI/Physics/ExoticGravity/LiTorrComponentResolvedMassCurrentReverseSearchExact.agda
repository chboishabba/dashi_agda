module DASHI.Physics.ExoticGravity.LiTorrComponentResolvedMassCurrentReverseSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- LI-TORR MEMORIAL PHYSICS: COMPONENT-RESOLVED REVERSE SEARCH
--
-- Reverse-search target for the current scientific wall.  This is a research
-- reconstruction schema, not a claim that the required empirical values are
-- already known or that Li/Torr established negative effective G.
------------------------------------------------------------------------

data SourceComponent : Set where
  ionicLattice : SourceComponent
  superconductingChargeCarrier : SourceComponent
  normalChargeCarrier : SourceComponent
  electromagneticFieldEnergy : SourceComponent
  mechanicalSupport : SourceComponent

record ComponentSourceDemand : Set where
  constructor component-source-demand
  field
    component : SourceComponent
    densityRequired : Bool
    massRequired : Bool
    chargeRequired : Bool
    velocityRequired : Bool
    spatialDistributionRequired : Bool
    phaseOrCoherenceRequired : Bool
    sourceLocator : String

open ComponentSourceDemand public

ionicLatticeDemand : ComponentSourceDemand
ionicLatticeDemand =
  component-source-demand ionicLattice true true true true true true
    "Li-Torr primary theory plus material/sample-specific source characterization"

superconductingCarrierDemand : ComponentSourceDemand
superconductingCarrierDemand =
  component-source-demand superconductingChargeCarrier true true true true true true
    "superconducting carrier density/mass/charge/velocity/coherence on the exact apparatus"

normalCarrierDemand : ComponentSourceDemand
normalCarrierDemand =
  component-source-demand normalChargeCarrier true true true true true false
    "normal-fluid/carrier contribution on the exact apparatus"

record MassCurrentReverseSearchBundle : Set where
  constructor mass-current-reverse-search-bundle
  field
    lattice : ComponentSourceDemand
    condensate : ComponentSourceDemand
    normalFraction : ComponentSourceDemand
    exactSampleGeometryRequired : Bool
    exactDriveWaveformRequired : Bool
    exactTemperaturePhaseStateRequired : Bool
    massCurrentDerivationRequired : Bool
    downstreamStressEnergyRequired : Bool

canonicalMassCurrentReverseSearchBundle : MassCurrentReverseSearchBundle
canonicalMassCurrentReverseSearchBundle =
  mass-current-reverse-search-bundle
    ionicLatticeDemand superconductingCarrierDemand normalCarrierDemand
    true true true true true

currentResidual : Current.MassCurrentResidual
currentResidual = Current.missingComponentVelocity

currentProducer : Search.ProducerClass
currentProducer = Current.producerForMassCurrentResidual currentResidual

record LiTorrMassCurrentBoundary : Set where
  constructor li-torr-mass-current-boundary
  field
    netElectricalCurrentDeterminesMassCurrent : Bool
    publishedTheoryAlonePaysExactApparatusSource : Bool
    materialStateMayChangeComponentMassCurrent : Bool
    componentResolvedMassCurrentAutomaticallyProvesNegativeG : Bool
    fullStressEnergyStillRequired : Bool
    ordinaryGRComparatorStillRequired : Bool

canonicalLiTorrMassCurrentBoundary : LiTorrMassCurrentBoundary
canonicalLiTorrMassCurrentBoundary =
  li-torr-mass-current-boundary false false true false true true
