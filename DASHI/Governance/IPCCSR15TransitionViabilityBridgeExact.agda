module DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base

------------------------------------------------------------------------
-- PRIMARY SOURCE: IPCC Special Report on Global Warming of 1.5 C (SR1.5).
--
-- Provenance class: PRIMARY SOURCE for statements in `SR15SourceBoundary`;
-- DASHI-DERIVED for the abstract relevance relation to the existing viability
-- axes.  No claim is made that SR1.5 endorses federated governance or bolo'bolo.
------------------------------------------------------------------------

record SR15SourceBoundary : Set where
  constructor sr15SourceBoundary
  field
    sourceInstitution : String
    sourceTitle : String
    sourceURL : String

    rapidFarReachingSystemTransitions : Bool
    energyTransitionNamed : Bool
    landTransitionNamed : Bool
    urbanInfrastructureTransitionNamed : Bool
    industrialTransitionNamed : Bool

    mitigationPortfolioHasSynergiesAndTradeoffs : Bool
    lowEnergyDemandPathwaysHaveStrongSDSynergies : Bool
    lowEnergyDemandPathwaysHaveFewerSDTradeoffs : Bool
    transitionManagementMatters : Bool
    localCommunitiesNamedAsImplementationCapacityActors : Bool

open SR15SourceBoundary public

canonicalSR15SourceBoundary : SR15SourceBoundary
canonicalSR15SourceBoundary =
  sr15SourceBoundary
    "Intergovernmental Panel on Climate Change"
    "Global Warming of 1.5 C - Summary for Policymakers / Chapter 5"
    "https://www.ipcc.ch/sr15/"
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- DASHI-derived relevance relation.
--
-- This does not turn an IPCC system-transition category into a proof that a
-- specific state satisfies any `ViabilityEnvelope` predicate.  It only records
-- which existing abstract axes would need evidence in a concrete application.
------------------------------------------------------------------------

data SR15TransitionDimension : Set where
  energyDimension : SR15TransitionDimension
  landDimension : SR15TransitionDimension
  urbanInfrastructureDimension : SR15TransitionDimension
  industrialDimension : SR15TransitionDimension
  sustainableDevelopmentTradeoffDimension : SR15TransitionDimension
  localImplementationCapacityDimension : SR15TransitionDimension

data ViabilityAxis : Set where
  governanceAxis : ViabilityAxis
  ecologicalAxis : ViabilityAxis
  resourceAxis : ViabilityAxis
  basicNeedsAxis : ViabilityAxis

data RelevantTo : SR15TransitionDimension → ViabilityAxis → Set where
  energyRelevantToResource : RelevantTo energyDimension resourceAxis
  energyRelevantToEcology : RelevantTo energyDimension ecologicalAxis
  landRelevantToEcology : RelevantTo landDimension ecologicalAxis
  landRelevantToBasicNeeds : RelevantTo landDimension basicNeedsAxis
  urbanRelevantToResource : RelevantTo urbanInfrastructureDimension resourceAxis
  urbanRelevantToBasicNeeds : RelevantTo urbanInfrastructureDimension basicNeedsAxis
  industryRelevantToResource : RelevantTo industrialDimension resourceAxis
  tradeoffRelevantToBasicNeeds :
    RelevantTo sustainableDevelopmentTradeoffDimension basicNeedsAxis
  tradeoffRelevantToEcology :
    RelevantTo sustainableDevelopmentTradeoffDimension ecologicalAxis
  localCapacityRelevantToGovernance :
    RelevantTo localImplementationCapacityDimension governanceAxis

record SR15ViabilitySocket (State : Set) : Set₁ where
  constructor sr15ViabilitySocket
  field
    envelope : Base.ViabilityEnvelope State
    energyEvidenceRequired : State → Set
    landEvidenceRequired : State → Set
    urbanInfrastructureEvidenceRequired : State → Set
    industrialEvidenceRequired : State → Set
    tradeoffEvidenceRequired : State → Set
    localImplementationCapacityEvidenceRequired : State → Set

open SR15ViabilitySocket public

record SR15BridgeBoundary : Set where
  constructor sr15BridgeBoundary
  field
    sr15ProvesFederatedGovernanceViable : Bool
    sr15ProvesBoloBoloMeetsClimateTargets : Bool
    sr15ProvesAnyConcreteDASHIStateViable : Bool
    lowDemandSynergyImpliesZeroTradeoffs : Bool
    sourceCategoriesEqualDASHIViabilityAxes : Bool
    dashiRelevanceRelationIsDerived : Bool
    concreteInstantiationNeedsAdditionalEvidence : Bool

open SR15BridgeBoundary public

canonicalSR15BridgeBoundary : SR15BridgeBoundary
canonicalSR15BridgeBoundary =
  sr15BridgeBoundary
    false
    false
    false
    false
    false
    true
    true

canonicalSR15TransitionViabilityBridgeReceipt : GenericReceipt.GenericReceipt
canonicalSR15TransitionViabilityBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "IPCC SR1.5 transition / viability evidence bridge"
    "DASHI.Governance.IPCCSR15TransitionViabilityBridgeExact"
    "canonicalSR15BridgeBoundary"
    "records source-qualified rapid system-transition, portfolio trade-off and low-energy-demand synergy statements and maps their evidentiary relevance into the existing abstract governance/ecology/resource/basic-needs viability axes"
    "SR1.5 does not prove federated governance or bolo'bolo viable, and the DASHI relevance relation is an explicitly derived adapter rather than an IPCC formalism"
    "agda -i . DASHI/Governance/IPCCSR15TransitionViabilityBridgeRegression.agda"
