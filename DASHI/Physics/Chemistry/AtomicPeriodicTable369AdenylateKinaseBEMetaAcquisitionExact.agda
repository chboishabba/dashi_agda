module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty

------------------------------------------------------------------------
-- SOURCE-PAID BE-META ACQUISITION ENVELOPE
--
-- Li, Liu & Ji explicitly report the bias-exchange metadynamics coordinate
-- walls and bias/sampling protocol.  These are simulation-method coordinates,
-- not state values and not experimental kinetics.  They therefore live beside,
-- not inside, the still-sparse per-state/per-edge calibration ledger.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Attr.articleDOI
articlePMID : Identity.ExternalIdentityDemand
articlePMID = Attr.articlePMID
articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Attr.articlePMCID
articleQID : Identity.ExternalIdentityDemand
articleQID = Attr.articleQID
adkQID : Identity.ExternalIdentityDemand
adkQID = Attr.adkQID
adkUniProt : Identity.ExternalIdentityDemand
adkUniProt = Attr.adkUniProt

record BEMetaProtocol : Set where
  constructor be-meta-protocol
  field
    thetaOneLowerDegrees : Nat
    thetaOneUpperDegrees : Nat
    thetaTwoLowerDegrees : Nat
    thetaTwoUpperDegrees : Nat
    dLnLowerAngstrom : Nat
    dLnUpperAngstrom : Nat
    gaussianHeightHundredthsKcalMol : Nat
    angularGaussianWidthHundredthsRadian : Nat
    dLnGaussianWidthTenthsAngstrom : Nat
    gaussianDepositionPicoseconds : Nat
    swapAttemptPicoseconds : Nat
    nanosecondsPerReplica : Nat
    replicaCount : Nat
    totalNanosecondsPerBEMeta : Nat
    coordinateSavePicoseconds : Nat
    energySaveHundredthsPicoseconds : Nat
    temperatureKelvin : Nat
    pressureBar : Nat
    sourceLocator : String
    methodRole : String
open BEMetaProtocol public

canonicalBEMetaProtocol : BEMetaProtocol
canonicalBEMetaProtocol = be-meta-protocol
  58 100
  20 70
  15 45
  5
  1
  1
  1
  2
  200
  4
  800
  5
  5
  300
  1
  "Li-Liu-Ji 2015 Materials and Methods, BE-META paragraph in PMCID PMC4572606"
  "source-paid simulation protocol: three CV walls and bias-exchange metadynamics acquisition settings; not a state calibration or experimental measurement"

freeEnergyUncertainty = Uncertainty.metadynamicsFreeEnergyUncertainty

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SimulationWallIsObservedState : Set where
data GaussianBiasParameterIsPhysicalFreeEnergy : Set where
data SamplingDurationProvesConvergenceEverywhere : Set where
data ProtocolIdentityPaysMissingStateValue : Set where

data ArticleQidCreatesMethodAuthority : Set where

simulationWallDoesNotCreateObservedState : SimulationWallIsObservedState → ⊥
simulationWallDoesNotCreateObservedState ()

gaussianBiasDoesNotBecomePhysicalFreeEnergy : GaussianBiasParameterIsPhysicalFreeEnergy → ⊥
gaussianBiasDoesNotBecomePhysicalFreeEnergy ()

samplingDurationDoesNotProveUniversalConvergence : SamplingDurationProvesConvergenceEverywhere → ⊥
samplingDurationDoesNotProveUniversalConvergence ()

protocolDoesNotPayMissingStateValue : ProtocolIdentityPaysMissingStateValue → ⊥
protocolDoesNotPayMissingStateValue ()

qidDoesNotCreateMethodAuthority : ArticleQidCreatesMethodAuthority → ⊥
qidDoesNotCreateMethodAuthority ()

record AdKBEMetaAcquisitionBoundary : Set where
  constructor adk-be-meta-acquisition-boundary
  field
    threeCVWallsPaid : Bool
    gaussianBiasProtocolPaid : Bool
    samplingCadencePaid : Bool
    replicaDurationPaid : Bool
    totalSimulationDurationPaid : Bool
    freeEnergyUncertaintyEnvelopeRetained : Bool
    doiPmidPmcidRetained : Bool
    articleQidMayRemainUnresolved : Bool
    protocolPaysIntermediateDLn : Bool
    protocolPaysPerStateFreeEnergy : Bool
    protocolPaysPerEdgeKramersRate : Bool
    protocolEqualsExperimentalMethod : Bool
open AdKBEMetaAcquisitionBoundary public

canonicalAdKBEMetaAcquisitionBoundary : AdKBEMetaAcquisitionBoundary
canonicalAdKBEMetaAcquisitionBoundary = adk-be-meta-acquisition-boundary
  true true true true true true true true
  false false false false
