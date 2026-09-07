module DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Papers.CoreTheoremInterfaces as Core
import DASHI.Analysis.RiemannZetaProgramBoundary as RH
import DASHI.Physics.GR.StressEnergyCompatibility as GR
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.Laws.PhysicalLawRecoveryBoundary as Laws

------------------------------------------------------------------------
-- ANTIGRAVITY x YM / NS / RH / GR / OBSERVATION / UNIFICATION
--
-- Cross-domain relevance is typed.  A shared mathematical or experimental
-- coordinate is not a proof transfer.  Gravitational observations now provide
-- the empirical GR-facing comparator layer between local anomaly claims and
-- theory/unification residuals.
------------------------------------------------------------------------

data InteractionDomain : Set where
  gravitationalObservation : InteractionDomain
  generalRelativity : InteractionDomain
  yangMills : InteractionDomain
  navierStokes : InteractionDomain
  riemannHypothesis : InteractionDomain
  unification : InteractionDomain

data InteractionRole : Set where
  empiricalComparator : InteractionRole
  directPhysicalDiscriminator : InteractionRole
  ordinaryConfounderClosure : InteractionRole
  sourceModelConstraint : InteractionRole
  structuralMethodOnly : InteractionRole
  promotionFirewall : InteractionRole

interactionRole : InteractionDomain → InteractionRole
interactionRole gravitationalObservation = empiricalComparator
interactionRole generalRelativity = directPhysicalDiscriminator
interactionRole yangMills = sourceModelConstraint
interactionRole navierStokes = ordinaryConfounderClosure
interactionRole riemannHypothesis = structuralMethodOnly
interactionRole unification = promotionFirewall

interactionNote : InteractionDomain → String
interactionNote gravitationalObservation =
  "Observation is an empirical comparator: calibrated strain, timing, orbital, free-fall, clock/redshift, or local-acceleration receipts constrain gravity models without becoming antigravity receipts by themselves."
interactionNote generalRelativity =
  "GR is the direct physical comparison lane: stress-energy, geodesic/free-fall, metric/clock response, wave propagation, and energy-condition consistency."
interactionNote yangMills =
  "YM may constrain coherent/high-field gauge-sector source models, but a gauge-field calculation is not an antigravity receipt and antigravity evidence is not a YM mass-gap proof."
interactionNote navierStokes =
  "NS/continuum-fluid reasoning is an ordinary-physics exclusion lane for ion wind, plasma, gas flow, thermal convection, vibration-mediated transport, and momentum exchange."
interactionNote riemannHypothesis =
  "RH contributes only structural proof-search motifs such as spectral positivity, exact identity, and fail-closed promotion; no physical causal bridge to antigravity is asserted."
interactionNote unification =
  "Unification is a consumer boundary: cross-sector agreement can generate residuals, but no terminal unification promotion follows from an antigravity anomaly or gravitational-wave observation."

------------------------------------------------------------------------
-- Claim-specific interaction routing.
------------------------------------------------------------------------

data CrossDomainDemand : Set where
  requireStressEnergyAndGeodesicCheck : CrossDomainDemand
  requireGaugeSourceAndOrdinaryEMCheck : CrossDomainDemand
  requireFluidPlasmaMomentumClosure : CrossDomainDemand
  requireGravitationalObservationComparator : CrossDomainDemand
  requireSpectralMethodSeparation : CrossDomainDemand
  requireUnificationPromotionFirewall : CrossDomainDemand

primaryCrossDomainDemand : Anti.AntigravityClaim → CrossDomainDemand
primaryCrossDomainDemand Anti.reducedPassiveWeight = requireStressEnergyAndGeodesicCheck
primaryCrossDomainDemand Anti.changedFreeFallResponse = requireGravitationalObservationComparator
primaryCrossDomainDemand Anti.remoteRepulsiveField = requireGravitationalObservationComparator
primaryCrossDomainDemand Anti.alteredInertialResponse = requireGaugeSourceAndOrdinaryEMCheck
primaryCrossDomainDemand Anti.persistentPropulsiveImpulse = requireFluidPlasmaMomentumClosure
primaryCrossDomainDemand Anti.engineeredMetricResponse = requireGravitationalObservationComparator

observationChannelForClaim : Anti.AntigravityClaim → Obs.GravitationalObservationChannel
observationChannelForClaim Anti.reducedPassiveWeight = Obs.freeFallEquivalence
observationChannelForClaim Anti.changedFreeFallResponse = Obs.freeFallEquivalence
observationChannelForClaim Anti.remoteRepulsiveField = Obs.localTestMassAcceleration
observationChannelForClaim Anti.alteredInertialResponse = Obs.freeFallEquivalence
observationChannelForClaim Anti.persistentPropulsiveImpulse = Obs.localTestMassAcceleration
observationChannelForClaim Anti.engineeredMetricResponse = Obs.clockOrRedshift

------------------------------------------------------------------------
-- Observation-theory comparison hierarchy.
------------------------------------------------------------------------

data ObservationTheoryStatus : Set where
  calibratedObservationNeeded : ObservationTheoryStatus
  ordinaryGRComparatorNeeded : ObservationTheoryStatus
  modifiedGravityComparatorNeeded : ObservationTheoryStatus
  crossSectorResidualOpen : ObservationTheoryStatus

record ObservationTheoryComparison : Set where
  constructor observation-theory-comparison
  field
    observation : Obs.GravitationalObservationReceipt
    ordinaryGRPredictionCarrier : String
    modifiedGravityPredictionCarrier : String
    ordinaryResidualClosed : Bool
    modifiedResidualSmaller : Bool
    sameObservableCompared : Bool
    status : ObservationTheoryStatus

open ObservationTheoryComparison public

record AntigravityUnificationBoundary : Set where
  constructor antigravity-unification-boundary
  field
    gravitationalObservationIsEmpiricalComparator : Bool
    grIsDirectPhysicsLane : Bool
    ymCanConstrainHighFieldSourceModels : Bool
    nsCanCloseOrdinaryMomentumConfounders : Bool
    rhHasDirectPhysicalAntigravityCausalRole : Bool
    sharedSpectralLanguageTransfersRHProof : Bool
    antigravityEvidenceTransfersYMMassGapProof : Bool
    antigravityEvidenceTransfersNSClayProof : Bool
    gravitationalWaveObservationProvesAntigravity : Bool
    gravitationalWaveObservationProvesModifiedGravity : Bool
    antigravityAnomalyPromotesSourcedEinsteinLaw : Bool
    antigravityAnomalyPromotesTerminalUnification : Bool
    crossDomainResidualsMayRefineExperimentDesign : Bool

canonicalAntigravityUnificationBoundary : AntigravityUnificationBoundary
canonicalAntigravityUnificationBoundary =
  antigravity-unification-boundary
    true true true true false false false false false false false false true

------------------------------------------------------------------------
-- Existing fail-closed theorem/program/observation boundaries are imported by
-- identity.
------------------------------------------------------------------------

existingCoreTheoremInterfaces : Core.CoreTheoremInterfaces
existingCoreTheoremInterfaces = Core.canonicalCoreTheoremInterfaces

existingRiemannBoundary : RH.CurrentZetaBoundary
existingRiemannBoundary = RH.currentZetaBoundary

existingGRStressEnergyBoundary : GR.StressEnergyBoundaryInterface
existingGRStressEnergyBoundary = GR.canonicalStressEnergyBoundaryInterface

existingGravitationalObservationBoundary : Obs.GravitationalObservationBoundary
existingGravitationalObservationBoundary = Obs.canonicalGravitationalObservationBoundary

existingCurrentObservationalStatus : Obs.CurrentObservationalStatusBoundary
existingCurrentObservationalStatus = Obs.canonicalCurrentObservationalStatusBoundary

------------------------------------------------------------------------
-- Explicit promotion firewall.
------------------------------------------------------------------------

coreNavierStokesStillFalse :
  Core.coreNavierStokesTerminalFalse ≡ Core.coreNavierStokesTerminalFalse
coreNavierStokesStillFalse = refl

coreYangMillsStillFalse :
  Core.coreYangMillsTerminalFalse ≡ Core.coreYangMillsTerminalFalse
coreYangMillsStillFalse = refl

coreUnificationStillFalse :
  Core.coreUnificationTerminalFalse ≡ Core.coreUnificationTerminalFalse
coreUnificationStillFalse = refl

record ResearchPriority : Set where
  constructor research-priority
  field
    domain : InteractionDomain
    role : InteractionRole
    note : String

canonicalResearchPriorities : List ResearchPriority
canonicalResearchPriorities =
  research-priority gravitationalObservation (interactionRole gravitationalObservation)
    (interactionNote gravitationalObservation)
  ∷ research-priority generalRelativity (interactionRole generalRelativity)
    (interactionNote generalRelativity)
  ∷ research-priority navierStokes (interactionRole navierStokes)
    (interactionNote navierStokes)
  ∷ research-priority yangMills (interactionRole yangMills)
    (interactionNote yangMills)
  ∷ research-priority riemannHypothesis (interactionRole riemannHypothesis)
    (interactionNote riemannHypothesis)
  ∷ research-priority unification (interactionRole unification)
    (interactionNote unification)
  ∷ []

------------------------------------------------------------------------
-- Physical-law recovery remains open at the exact existing obligations.  A
-- novel anomaly or GW residual may motivate a new empirical residual, but does
-- not discharge YM mass gap, NS regularity, GR continuum/initial-value control,
-- quantum-gravity, RH, or universal-theory obligations.
------------------------------------------------------------------------

physicalLawBoundaryTypeAvailable : Setω
physicalLawBoundaryTypeAvailable = Laws.PhysicalLawRecoveryBoundary
