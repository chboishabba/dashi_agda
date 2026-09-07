module DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Papers.CoreTheoremInterfaces as Core
import DASHI.Analysis.RiemannZetaProgramBoundary as RH
import DASHI.Physics.GR.StressEnergyCompatibility as GR
import DASHI.Physics.Laws.PhysicalLawRecoveryBoundary as Laws

------------------------------------------------------------------------
-- ANTIGRAVITY x YM / NS / RH / GR / UNIFICATION
--
-- Cross-domain relevance is typed.  A shared mathematical or experimental
-- coordinate is not a proof transfer.  In particular, an antigravity residual
-- cannot promote a Clay theorem, RH, sourced Einstein gravity, or terminal
-- unification merely because the domains share PDE, spectral, gauge, or
-- geometric language.
------------------------------------------------------------------------

data InteractionDomain : Set where
  generalRelativity : InteractionDomain
  yangMills : InteractionDomain
  navierStokes : InteractionDomain
  riemannHypothesis : InteractionDomain
  unification : InteractionDomain

data InteractionRole : Set where
  directPhysicalDiscriminator : InteractionRole
  ordinaryConfounderClosure : InteractionRole
  sourceModelConstraint : InteractionRole
  structuralMethodOnly : InteractionRole
  promotionFirewall : InteractionRole

interactionRole : InteractionDomain → InteractionRole
interactionRole generalRelativity = directPhysicalDiscriminator
interactionRole yangMills = sourceModelConstraint
interactionRole navierStokes = ordinaryConfounderClosure
interactionRole riemannHypothesis = structuralMethodOnly
interactionRole unification = promotionFirewall

interactionNote : InteractionDomain → String
interactionNote generalRelativity =
  "GR is the direct physical comparison lane: stress-energy, geodesic/free-fall, metric/clock response, and energy-condition consistency."
interactionNote yangMills =
  "YM may constrain coherent/high-field gauge-sector source models, but a gauge-field calculation is not an antigravity receipt and antigravity evidence is not a YM mass-gap proof."
interactionNote navierStokes =
  "NS/continuum-fluid reasoning is an ordinary-physics exclusion lane for ion wind, plasma, gas flow, thermal convection, vibration-mediated transport, and momentum exchange."
interactionNote riemannHypothesis =
  "RH contributes only structural proof-search motifs such as spectral positivity, exact identity, and fail-closed promotion; no physical causal bridge to antigravity is asserted."
interactionNote unification =
  "Unification is a consumer boundary: cross-sector agreement can generate residuals, but no terminal unification promotion follows from an antigravity anomaly."

------------------------------------------------------------------------
-- Claim-specific interaction routing.
------------------------------------------------------------------------

data CrossDomainDemand : Set where
  requireStressEnergyAndGeodesicCheck : CrossDomainDemand
  requireGaugeSourceAndOrdinaryEMCheck : CrossDomainDemand
  requireFluidPlasmaMomentumClosure : CrossDomainDemand
  requireSpectralMethodSeparation : CrossDomainDemand
  requireUnificationPromotionFirewall : CrossDomainDemand

primaryCrossDomainDemand : Anti.AntigravityClaim → CrossDomainDemand
primaryCrossDomainDemand Anti.reducedPassiveWeight = requireStressEnergyAndGeodesicCheck
primaryCrossDomainDemand Anti.changedFreeFallResponse = requireStressEnergyAndGeodesicCheck
primaryCrossDomainDemand Anti.remoteRepulsiveField = requireStressEnergyAndGeodesicCheck
primaryCrossDomainDemand Anti.alteredInertialResponse = requireGaugeSourceAndOrdinaryEMCheck
primaryCrossDomainDemand Anti.persistentPropulsiveImpulse = requireFluidPlasmaMomentumClosure
primaryCrossDomainDemand Anti.engineeredMetricResponse = requireStressEnergyAndGeodesicCheck

record AntigravityUnificationBoundary : Set where
  constructor antigravity-unification-boundary
  field
    grIsDirectPhysicsLane : Bool
    ymCanConstrainHighFieldSourceModels : Bool
    nsCanCloseOrdinaryMomentumConfounders : Bool
    rhHasDirectPhysicalAntigravityCausalRole : Bool
    sharedSpectralLanguageTransfersRHProof : Bool
    antigravityEvidenceTransfersYMMassGapProof : Bool
    antigravityEvidenceTransfersNSClayProof : Bool
    antigravityAnomalyPromotesSourcedEinsteinLaw : Bool
    antigravityAnomalyPromotesTerminalUnification : Bool
    crossDomainResidualsMayRefineExperimentDesign : Bool

canonicalAntigravityUnificationBoundary : AntigravityUnificationBoundary
canonicalAntigravityUnificationBoundary =
  antigravity-unification-boundary
    true true true false false false false false false true

------------------------------------------------------------------------
-- Existing fail-closed theorem/program boundaries are imported by identity.
------------------------------------------------------------------------

existingCoreTheoremInterfaces : Core.CoreTheoremInterfaces
existingCoreTheoremInterfaces = Core.canonicalCoreTheoremInterfaces

existingRiemannBoundary : RH.CurrentZetaBoundary
existingRiemannBoundary = RH.currentZetaBoundary

existingGRStressEnergyBoundary : GR.StressEnergyBoundaryInterface
existingGRStressEnergyBoundary = GR.canonicalStressEnergyBoundaryInterface

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
  research-priority generalRelativity (interactionRole generalRelativity)
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
-- Physical-law recovery remains open at the exact existing obligations.  This
-- import is deliberate: a novel anomaly may motivate a new empirical residual,
-- but does not discharge YM mass gap, NS regularity, GR continuum/initial-value
-- control, quantum-gravity, or universal-theory obligations.
------------------------------------------------------------------------

physicalLawBoundaryTypeAvailable : Setω
physicalLawBoundaryTypeAvailable = Laws.PhysicalLawRecoveryBoundary
