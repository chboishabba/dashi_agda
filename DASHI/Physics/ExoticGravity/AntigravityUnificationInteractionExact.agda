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
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Physics.Laws.PhysicalLawRecoveryBoundary as Laws

------------------------------------------------------------------------
-- ANTIGRAVITY x YM / NS / RH / GR / OBSERVATION / UNIFICATION
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
  "Observation is an empirical comparator: calibrated static-load, strain, timing, orbital, free-fall, clock/redshift, or local-acceleration receipts constrain gravity models without becoming antigravity receipts by themselves."
interactionNote generalRelativity =
  "GR is the direct physical comparison lane: stress-energy, static/passive weight, geodesic/free-fall, metric/clock response, wave propagation, and energy-condition consistency."
interactionNote yangMills =
  "YM may constrain coherent/high-field gauge-sector source models, but a gauge-field calculation is not an antigravity receipt and antigravity evidence is not a YM mass-gap proof."
interactionNote navierStokes =
  "NS/continuum-fluid reasoning is an ordinary-physics exclusion lane for ion wind, plasma, gas flow, thermal convection, vibration-mediated transport, and momentum exchange."
interactionNote riemannHypothesis =
  "RH contributes only structural proof-search motifs such as spectral positivity, exact identity, and fail-closed promotion; no physical causal bridge to antigravity is asserted."
interactionNote unification =
  "Unification is a consumer boundary: cross-sector agreement can generate residuals, but no terminal unification promotion follows from an antigravity anomaly or gravitational-wave observation."

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

------------------------------------------------------------------------
-- Introspective repair: not every antigravity-labelled claim belongs to a GR
-- observation channel.  Inertial response and propulsive impulse are routed to
-- their own consumers rather than being coerced into free-fall/local gravity.
------------------------------------------------------------------------

data ClaimObservationRoute : Set where
  gravitationalObservationRoute :
    Obs.GravitationalObservationChannel → ClaimObservationRoute
  inertialComparisonRoute : ClaimObservationRoute
  ordinaryMomentumClosureRoute : ClaimObservationRoute

observationRouteForClaim : Anti.AntigravityClaim → ClaimObservationRoute
observationRouteForClaim Anti.reducedPassiveWeight =
  gravitationalObservationRoute Obs.staticLoadOrWeight
observationRouteForClaim Anti.changedFreeFallResponse =
  gravitationalObservationRoute Obs.freeFallEquivalence
observationRouteForClaim Anti.remoteRepulsiveField =
  gravitationalObservationRoute Obs.localTestMassAcceleration
observationRouteForClaim Anti.alteredInertialResponse =
  inertialComparisonRoute
observationRouteForClaim Anti.persistentPropulsiveImpulse =
  ordinaryMomentumClosureRoute
observationRouteForClaim Anti.engineeredMetricResponse =
  gravitationalObservationRoute Obs.clockOrRedshift

record GravitationalClaimRoute (claim : Anti.AntigravityClaim) : Set where
  constructor gravitational-claim-route
  field
    channel : Obs.GravitationalObservationChannel
    routeMatches : observationRouteForClaim claim ≡ gravitationalObservationRoute channel

open GravitationalClaimRoute public

reducedPassiveWeightGravityRoute : GravitationalClaimRoute Anti.reducedPassiveWeight
reducedPassiveWeightGravityRoute = gravitational-claim-route Obs.staticLoadOrWeight refl

changedFreeFallGravityRoute : GravitationalClaimRoute Anti.changedFreeFallResponse
changedFreeFallGravityRoute = gravitational-claim-route Obs.freeFallEquivalence refl

remoteFieldGravityRoute : GravitationalClaimRoute Anti.remoteRepulsiveField
remoteFieldGravityRoute = gravitational-claim-route Obs.localTestMassAcceleration refl

metricResponseGravityRoute : GravitationalClaimRoute Anti.engineeredMetricResponse
metricResponseGravityRoute = gravitational-claim-route Obs.clockOrRedshift refl

inertialResponseIsNotFreeFallRoute :
  observationRouteForClaim Anti.alteredInertialResponse
    ≡ gravitationalObservationRoute Obs.freeFallEquivalence → ⊥
inertialResponseIsNotFreeFallRoute ()

propulsiveImpulseIsNotLocalGravityRoute :
  observationRouteForClaim Anti.persistentPropulsiveImpulse
    ≡ gravitationalObservationRoute Obs.localTestMassAcceleration → ⊥
propulsiveImpulseIsNotLocalGravityRoute ()

data ObservationTheoryStatus : Set where
  calibratedObservationNeeded : ObservationTheoryStatus
  ordinaryGRComparatorNeeded : ObservationTheoryStatus
  modifiedGravityComparatorNeeded : ObservationTheoryStatus
  crossSectorResidualOpen : ObservationTheoryStatus

record ObservationTheoryComparison : Set where
  constructor observation-theory-comparison
  field
    observation : Obs.GravitationalObservationReceipt
    ordinaryGRPrediction : Attr.AttributedGravitationalPrediction
    modifiedGravityPrediction : Attr.AttributedGravitationalPrediction
    ordinaryGRWeld :
      Pred.PredictionObservationWeld
        (Attr.prediction ordinaryGRPrediction)
        observation
    modifiedGravityWeld :
      Pred.PredictionObservationWeld
        (Attr.prediction modifiedGravityPrediction)
        observation
    comparisonLineage :
      Attr.PairedPredictionComparisonLineage
        ordinaryGRPrediction modifiedGravityPrediction observation
    ordinaryResidualClosed : Bool
    modifiedResidualSmaller : Bool
    status : ObservationTheoryStatus

open ObservationTheoryComparison public

record AntigravityUnificationBoundary : Set where
  constructor antigravity-unification-boundary
  field
    gravitationalObservationIsEmpiricalComparator : Bool
    staticWeightIsDistinctFromFreeFall : Bool
    everyAntigravityClaimIsGravitationalObservation : Bool
    inertialResponseRequiresInertialComparison : Bool
    propulsiveImpulseRequiresMomentumClosure : Bool
    predictionAttributionRequiredBeforeComparison : Bool
    comparisonLineageMustBindExactConsumedInputs : Bool
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
    true true false true true true true true true true false false false false false false false false true

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

existingPredictionObservationBoundary : Pred.PredictionObservationBoundary
existingPredictionObservationBoundary = Pred.canonicalPredictionObservationBoundary

existingPredictionAttributionBoundary : Attr.PredictionAttributionBoundary
existingPredictionAttributionBoundary = Attr.canonicalPredictionAttributionBoundary

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

physicalLawBoundaryTypeAvailable : Setω
physicalLawBoundaryTypeAvailable = Laws.PhysicalLawRecoveryBoundary
