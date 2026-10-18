module DASHI.Biology.Agriculture.DrylandRegenerationNitrogenFactorisationExact where

------------------------------------------------------------------------
-- DRYLAND REGENERATION NITROGEN EVIDENCE FACTORISATION
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- This owner applies the repository's existing intersectional
-- non-factorability and Snowball discovery machinery to the nitrogen
-- transport/carryover distinctions already source-bounded by the agriculture
-- owners.
--
-- The finite worlds below are synthetic DASHI witnesses. They do NOT assert
-- that any particular empirical paper observed both worlds. Their purpose is
-- representation-theoretic: a coarse observation cannot determine a consumer
-- that distinguishes two states which that observation collapses.
--
-- Consequently:
--
--   fixed-N label        cannot determine transport route;
--   released-N label     cannot determine demand-time crop capture;
--   N-service summary    cannot determine a water-coupled outcome;
--   carryover label      cannot determine fertilizer replacement value.
--
-- Each failed factorisation is also routed to the existing Snowball discovery
-- interface as a missing-axis / experimental-design demand. Proposal is not
-- evidence and does not close any canonical BNF stage.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery

------------------------------------------------------------------------
-- Fixed N is not a transport-route identifier.
------------------------------------------------------------------------

data NitrogenTransportWorld : Set where
  fixedNViaLivingBelowGroundRoute : NitrogenTransportWorld
  fixedNViaResidueMineralisationRoute : NitrogenTransportWorld

data FixedNitrogenToken : Set where
  fixedNitrogenObserved : FixedNitrogenToken

fixedNitrogenProjection : NitrogenTransportWorld → FixedNitrogenToken
fixedNitrogenProjection _ = fixedNitrogenObserved

data TransportRouteOutcome : Set where
  livingBelowGroundRoute : TransportRouteOutcome
  residueMineralisationRoute : TransportRouteOutcome

transportRouteOutcome : NitrogenTransportWorld → TransportRouteOutcome
transportRouteOutcome fixedNViaLivingBelowGroundRoute = livingBelowGroundRoute
transportRouteOutcome fixedNViaResidueMineralisationRoute = residueMineralisationRoute

livingRouteNotResidueRoute :
  livingBelowGroundRoute ≡ residueMineralisationRoute → ⊥
livingRouteNotResidueRoute ()

fixedNitrogenRouteWitness :
  INF.NonFactorabilityWitness fixedNitrogenProjection transportRouteOutcome
fixedNitrogenRouteWitness =
  INF.nonFactorabilityWitness
    fixedNViaLivingBelowGroundRoute
    fixedNViaResidueMineralisationRoute
    refl
    livingRouteNotResidueRoute

fixedNitrogenCannotDetermineTransportRoute :
  INF.FactorsThrough fixedNitrogenProjection transportRouteOutcome → ⊥
fixedNitrogenCannotDetermineTransportRoute =
  INF.witnessRulesOutEveryFlatFactorisation fixedNitrogenRouteWitness

------------------------------------------------------------------------
-- Released N is not demand-time captured N.
------------------------------------------------------------------------

data NitrogenTimingWorld : Set where
  releaseAlignedWithConsumerDemand : NitrogenTimingWorld
  releaseLostBeforeConsumerDemand : NitrogenTimingWorld

data ReleasedNitrogenToken : Set where
  nitrogenReleased : ReleasedNitrogenToken

releasedNitrogenProjection : NitrogenTimingWorld → ReleasedNitrogenToken
releasedNitrogenProjection _ = nitrogenReleased

demandCaptureOutcome : NitrogenTimingWorld → Bool
demandCaptureOutcome releaseAlignedWithConsumerDemand = true
demandCaptureOutcome releaseLostBeforeConsumerDemand = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

releasedNitrogenTimingWitness :
  INF.NonFactorabilityWitness releasedNitrogenProjection demandCaptureOutcome
releasedNitrogenTimingWitness =
  INF.nonFactorabilityWitness
    releaseAlignedWithConsumerDemand
    releaseLostBeforeConsumerDemand
    refl
    trueNotFalse

releasedNitrogenCannotDetermineDemandCapture :
  INF.FactorsThrough releasedNitrogenProjection demandCaptureOutcome → ⊥
releasedNitrogenCannotDetermineDemandCapture =
  INF.witnessRulesOutEveryFlatFactorisation releasedNitrogenTimingWitness

------------------------------------------------------------------------
-- Nitrogen service is not sufficient with water erased.
------------------------------------------------------------------------

data NitrogenWaterWorld : Set where
  nitrogenServiceWithAdequateWater : NitrogenWaterWorld
  nitrogenServiceUnderWaterConstraint : NitrogenWaterWorld

data NitrogenServiceToken : Set where
  nitrogenServiceObserved : NitrogenServiceToken

nitrogenServiceProjection : NitrogenWaterWorld → NitrogenServiceToken
nitrogenServiceProjection _ = nitrogenServiceObserved

waterCoupledOutcome : NitrogenWaterWorld → Bool
waterCoupledOutcome nitrogenServiceWithAdequateWater = true
waterCoupledOutcome nitrogenServiceUnderWaterConstraint = false

nitrogenWaterWitness :
  INF.NonFactorabilityWitness nitrogenServiceProjection waterCoupledOutcome
nitrogenWaterWitness =
  INF.nonFactorabilityWitness
    nitrogenServiceWithAdequateWater
    nitrogenServiceUnderWaterConstraint
    refl
    trueNotFalse

nitrogenServiceCannotDetermineWaterCoupledOutcome :
  INF.FactorsThrough nitrogenServiceProjection waterCoupledOutcome → ⊥
nitrogenServiceCannotDetermineWaterCoupledOutcome =
  INF.witnessRulesOutEveryFlatFactorisation nitrogenWaterWitness

------------------------------------------------------------------------
-- Carryover evidence is not a fertilizer-replacement value.
------------------------------------------------------------------------

data FertilizerReplacementWorld : Set where
  sameCarryoverHighMineralNReplacement : FertilizerReplacementWorld
  sameCarryoverLowMineralNReplacement : FertilizerReplacementWorld

data CarryoverToken : Set where
  nitrogenCarryoverObserved : CarryoverToken

carryoverProjection : FertilizerReplacementWorld → CarryoverToken
carryoverProjection _ = nitrogenCarryoverObserved

data ReplacementOutcome : Set where
  largerReplacementValue : ReplacementOutcome
  smallerReplacementValue : ReplacementOutcome

replacementOutcome : FertilizerReplacementWorld → ReplacementOutcome
replacementOutcome sameCarryoverHighMineralNReplacement = largerReplacementValue
replacementOutcome sameCarryoverLowMineralNReplacement = smallerReplacementValue

largerNotSmaller :
  largerReplacementValue ≡ smallerReplacementValue → ⊥
largerNotSmaller ()

replacementCounterfactualWitness :
  INF.NonFactorabilityWitness carryoverProjection replacementOutcome
replacementCounterfactualWitness =
  INF.nonFactorabilityWitness
    sameCarryoverHighMineralNReplacement
    sameCarryoverLowMineralNReplacement
    refl
    largerNotSmaller

carryoverCannotDetermineReplacementValue :
  INF.FactorsThrough carryoverProjection replacementOutcome → ⊥
carryoverCannotDetermineReplacementValue =
  INF.witnessRulesOutEveryFlatFactorisation replacementCounterfactualWitness

------------------------------------------------------------------------
-- Enriched-observer repairs.
--
-- These finite repair theorems state only that the missing distinction is
-- sufficient for the synthetic witness consumer. They do not claim that the
-- listed coordinate set is universally sufficient for field deployment.
------------------------------------------------------------------------

data TransportRouteObservation : Set where
  observedLivingBelowGroundRoute : TransportRouteObservation
  observedResidueMineralisationRoute : TransportRouteObservation

transportRouteEnrichedProjection :
  NitrogenTransportWorld → TransportRouteObservation
transportRouteEnrichedProjection fixedNViaLivingBelowGroundRoute =
  observedLivingBelowGroundRoute
transportRouteEnrichedProjection fixedNViaResidueMineralisationRoute =
  observedResidueMineralisationRoute

interpretTransportRouteObservation :
  TransportRouteObservation → TransportRouteOutcome
interpretTransportRouteObservation observedLivingBelowGroundRoute =
  livingBelowGroundRoute
interpretTransportRouteObservation observedResidueMineralisationRoute =
  residueMineralisationRoute

transportRouteEnrichedFactorisation :
  INF.FactorsThrough transportRouteEnrichedProjection transportRouteOutcome
transportRouteEnrichedFactorisation =
  INF.factorsThrough interpretTransportRouteObservation factor
  where
    factor : ∀ state →
      transportRouteOutcome state ≡
      interpretTransportRouteObservation (transportRouteEnrichedProjection state)
    factor fixedNViaLivingBelowGroundRoute = refl
    factor fixedNViaResidueMineralisationRoute = refl

data ReleaseTimingObservation : Set where
  observedDemandAlignedRelease : ReleaseTimingObservation
  observedPreDemandLoss : ReleaseTimingObservation

releaseTimingEnrichedProjection :
  NitrogenTimingWorld → ReleaseTimingObservation
releaseTimingEnrichedProjection releaseAlignedWithConsumerDemand =
  observedDemandAlignedRelease
releaseTimingEnrichedProjection releaseLostBeforeConsumerDemand =
  observedPreDemandLoss

interpretReleaseTimingObservation : ReleaseTimingObservation → Bool
interpretReleaseTimingObservation observedDemandAlignedRelease = true
interpretReleaseTimingObservation observedPreDemandLoss = false

releaseTimingEnrichedFactorisation :
  INF.FactorsThrough releaseTimingEnrichedProjection demandCaptureOutcome
releaseTimingEnrichedFactorisation =
  INF.factorsThrough interpretReleaseTimingObservation factor
  where
    factor : ∀ state →
      demandCaptureOutcome state ≡
      interpretReleaseTimingObservation (releaseTimingEnrichedProjection state)
    factor releaseAlignedWithConsumerDemand = refl
    factor releaseLostBeforeConsumerDemand = refl

data NitrogenWaterObservation : Set where
  observedAdequateWater : NitrogenWaterObservation
  observedWaterConstraint : NitrogenWaterObservation

nitrogenWaterEnrichedProjection :
  NitrogenWaterWorld → NitrogenWaterObservation
nitrogenWaterEnrichedProjection nitrogenServiceWithAdequateWater =
  observedAdequateWater
nitrogenWaterEnrichedProjection nitrogenServiceUnderWaterConstraint =
  observedWaterConstraint

interpretNitrogenWaterObservation : NitrogenWaterObservation → Bool
interpretNitrogenWaterObservation observedAdequateWater = true
interpretNitrogenWaterObservation observedWaterConstraint = false

nitrogenWaterEnrichedFactorisation :
  INF.FactorsThrough nitrogenWaterEnrichedProjection waterCoupledOutcome
nitrogenWaterEnrichedFactorisation =
  INF.factorsThrough interpretNitrogenWaterObservation factor
  where
    factor : ∀ state →
      waterCoupledOutcome state ≡
      interpretNitrogenWaterObservation (nitrogenWaterEnrichedProjection state)
    factor nitrogenServiceWithAdequateWater = refl
    factor nitrogenServiceUnderWaterConstraint = refl

data ReplacementCounterfactualObservation : Set where
  observedHigherReplacementCurve : ReplacementCounterfactualObservation
  observedLowerReplacementCurve : ReplacementCounterfactualObservation

replacementCounterfactualEnrichedProjection :
  FertilizerReplacementWorld → ReplacementCounterfactualObservation
replacementCounterfactualEnrichedProjection sameCarryoverHighMineralNReplacement =
  observedHigherReplacementCurve
replacementCounterfactualEnrichedProjection sameCarryoverLowMineralNReplacement =
  observedLowerReplacementCurve

interpretReplacementCounterfactualObservation :
  ReplacementCounterfactualObservation → ReplacementOutcome
interpretReplacementCounterfactualObservation observedHigherReplacementCurve =
  largerReplacementValue
interpretReplacementCounterfactualObservation observedLowerReplacementCurve =
  smallerReplacementValue

replacementCounterfactualEnrichedFactorisation :
  INF.FactorsThrough
    replacementCounterfactualEnrichedProjection
    replacementOutcome
replacementCounterfactualEnrichedFactorisation =
  INF.factorsThrough interpretReplacementCounterfactualObservation factor
  where
    factor : ∀ state →
      replacementOutcome state ≡
      interpretReplacementCounterfactualObservation
        (replacementCounterfactualEnrichedProjection state)
    factor sameCarryoverHighMineralNReplacement = refl
    factor sameCarryoverLowMineralNReplacement = refl

------------------------------------------------------------------------
-- Failed factorisation -> missing-axis / experiment-design proposals.
--
-- These are DASHI planning receipts only. They do not create measurements.
------------------------------------------------------------------------

data NitrogenRepairAxis : Set where
  transportRouteAxis : NitrogenRepairAxis
  releaseDemandTimingAxis : NitrogenRepairAxis
  waterStateAxis : NitrogenRepairAxis
  mineralNResponseCurveAxis : NitrogenRepairAxis

transportRouteAxisProposal : Discovery.AxisProposal NitrogenRepairAxis
transportRouteAxisProposal =
  Discovery.axis-proposal
    transportRouteAxis
    Discovery.failedFactorsThrough
    "companion-grass nitrogen-route consumer"
    "does observed fixed N identify the downstream transport route?"
    "fixed-N projection collapses living-below-ground and residue-mineralisation worlds"
    "Queensland woody-legume/grass source identities and route receipts remain distinct"
    "proposal does not create living-root transfer evidence"

releaseDemandTimingAxisProposal : Discovery.AxisProposal NitrogenRepairAxis
releaseDemandTimingAxisProposal =
  Discovery.axis-proposal
    releaseDemandTimingAxis
    Discovery.experimentalDesign
    "following-crop nitrogen-availability consumer"
    "is released nitrogen available when the consumer demands it?"
    "released-N projection collapses aligned capture and pre-demand loss"
    "release, mineralisation, loss and crop capture remain separate source roles"
    "experimental design is requested; no crop-availability receipt is manufactured"

waterStateAxisProposal : Discovery.AxisProposal NitrogenRepairAxis
waterStateAxisProposal =
  Discovery.axis-proposal
    waterStateAxis
    Discovery.failedFactorsThrough
    "dryland nitrogen-service optimisation consumer"
    "does nitrogen-service evidence determine outcome with water state erased?"
    "same N-service projection permits adequate-water and water-constrained outcomes"
    "Queensland ley and dryland source systems retain hydrological context"
    "water-axis relevance does not create deployment authority"

mineralNCounterfactualAxisProposal : Discovery.AxisProposal NitrogenRepairAxis
mineralNCounterfactualAxisProposal =
  Discovery.axis-proposal
    mineralNResponseCurveAxis
    Discovery.experimentalDesign
    "fertilizer-replacement consumer"
    "what mineral-N response curve identifies the replacement value?"
    "carryover projection alone collapses worlds with different replacement outcomes"
    "annual-cover-crop counterfactual evidence remains comparator-only for Acacia/Senegalia"
    "experiment design does not close avoidedMineralN"

------------------------------------------------------------------------
-- Boundary / attribution.
------------------------------------------------------------------------

record NitrogenFactorisationBoundary : Set where
  constructor nitrogen-factorisation-boundary
  field
    fixedNRouteNonFactorabilityOwned : Bool
    releaseDemandTimingNonFactorabilityOwned : Bool
    nitrogenWaterNonFactorabilityOwned : Bool
    fertilizerCounterfactualNonFactorabilityOwned : Bool
    failedFactorisationMayProposeRepairAxis : Bool
    enrichedObserverRepairFactorisationsOwned : Bool
    enrichedFiniteRepairClaimedUniversallySufficient : Bool
    proposalCreatesEmpiricalEvidence : Bool
    finiteWitnessCreatesSourceProposition : Bool
    comparatorCreatesAcaciaSameObjectEvidence : Bool

open NitrogenFactorisationBoundary public

canonicalNitrogenFactorisationBoundary : NitrogenFactorisationBoundary
canonicalNitrogenFactorisationBoundary = record
  { fixedNRouteNonFactorabilityOwned = true
  ; releaseDemandTimingNonFactorabilityOwned = true
  ; nitrogenWaterNonFactorabilityOwned = true
  ; fertilizerCounterfactualNonFactorabilityOwned = true
  ; failedFactorisationMayProposeRepairAxis = true
  ; enrichedObserverRepairFactorisationsOwned = true
  ; enrichedFiniteRepairClaimedUniversallySufficient = false
  ; proposalCreatesEmpiricalEvidence = false
  ; finiteWitnessCreatesSourceProposition = false
  ; comparatorCreatesAcaciaSameObjectEvidence = false
  }

attributionRule : String
attributionRule =
  "DASHI owns the finite non-factorability witnesses, FactorsThrough exclusions, finite enriched-observer repair factorisations and Snowball axis proposals in this module. They are synthetic representation/experimental-design results, not propositions attributed to Vallis, Catchpoole & Blair, Hossain, Bell/Peoples, Fontes or any Acacia/Senegalia source. Empirical route, timing, water, crop-response and counterfactual claims remain owned by their source-specific agriculture modules. Failed factorisation may identify what an experiment must distinguish; it does not create the missing measurement, same-object relation, fertilizer-replacement value or deployment authority."
