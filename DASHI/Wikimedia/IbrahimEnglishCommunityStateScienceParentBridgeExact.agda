module DASHI.Wikimedia.IbrahimEnglishCommunityStateScienceParentBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishHighFlowFunnelCoverageExact as Funnel

------------------------------------------------------------------------
-- CURRENT EN PARENT BRIDGES FOR THREE IBRAHIM HIGH-FLOW FUNNELS
--
-- Ibrahim source:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001.
--
-- Current EN observations inspected 2026-09-10:
--   Community -> social unit
--   State     -> political entity
--   Science   -> knowledge
--
-- Current EN also makes the richer decompositions useful to DASHI explicit:
-- Community: place/norms/culture/religion/values/customs/identity.
-- State: society/population/territory/government/legitimacy/force.
-- Science: knowledge/nature/society/scientific method/evidence.
--
-- These are navigation coordinates, not definitions imposed on DASHI.
------------------------------------------------------------------------

record CurrentEnParentBridge : Set where
  constructor current-en-parent-bridge
  field
    childTitle : String
    childQid : String
    parentTitle : String
    parentQidResolution : String
    observationDate : String
    existingDashiSubstrate : String
    bridgeDebt : String
    parentIsProofDependency : Bool
open CurrentEnParentBridge public

communityToSocialUnit : CurrentEnParentBridge
communityToSocialUnit =
  current-en-parent-bridge
    "Community" "Q177634"
    "social unit" "qid-unresolved-in-this-tranche"
    "2026-09-10"
    "CommunityConnectednessTopology; CulturalMembershipBoundary; Indigenous/culture/place; governance/institutional/community-observation fibres"
    "canonical social-unit/community bridge preserving place, shared practice, identity and plural membership without presuming one spokesperson or homogeneous values"
    false

stateToPoliticalEntity : CurrentEnParentBridge
stateToPoliticalEntity =
  current-en-parent-bridge
    "State" "Q7275"
    "political entity" "qid-unresolved-in-this-tranche; Q1048835 is political territorial entity and is not silently substituted"
    "2026-09-10"
    "Governance; SensibLaw; Mabo/sovereignty; jurisdiction; territory; authority; political-science/politics bridge"
    "canonical State/Polity bridge must distinguish state from government, nation and society, and retain population, territory, authority, sovereignty and recognition as separate coordinates"
    false

scienceToKnowledge : CurrentEnParentBridge
scienceToKnowledge =
  current-en-parent-bridge
    "Science" "Q336"
    "knowledge" "Q9081"
    "2026-09-10"
    "BoundaryScienceEverything; MultiObserverScienceQuotient; source diligence; experiment/evidence; formal proof; natural/social/applied science domains"
    "canonical Science/Knowledge bridge must keep empirical evidence, formal deduction, source provenance, replication and observer plurality distinct; knowledge is broader than scientific knowledge"
    false

------------------------------------------------------------------------
-- Introspective bridge requirements.  These consume existing content rather
-- than creating a second social ontology or a universal theory of science.
------------------------------------------------------------------------

record CommunityBridgeRequirements : Set where
  constructor community-bridge-requirements
  field
    socialUnitCoordinate : Bool
    placeCoordinate : Bool
    cultureNormIdentityCoordinates : Bool
    pluralMembershipAllowed : Bool
    communityImpliesHomogeneity : Bool
open CommunityBridgeRequirements public

communityRequirements : CommunityBridgeRequirements
communityRequirements =
  community-bridge-requirements true true true true false

record StateBridgeRequirements : Set where
  constructor state-bridge-requirements
  field
    populationCoordinate : Bool
    territoryCoordinate : Bool
    governmentCoordinate : Bool
    sovereigntyCoordinate : Bool
    recognitionCoordinate : Bool
    stateEqualsGovernment : Bool
    stateEqualsNation : Bool
    stateEqualsSociety : Bool
open StateBridgeRequirements public

stateRequirements : StateBridgeRequirements
stateRequirements =
  state-bridge-requirements true true true true true false false false

record ScienceBridgeRequirements : Set where
  constructor science-bridge-requirements
  field
    knowledgeCoordinate : Bool
    empiricalEvidenceCoordinate : Bool
    formalDeductionCoordinate : Bool
    sourceProvenanceCoordinate : Bool
    replicationCoordinate : Bool
    pluralObserverCoordinate : Bool
    scienceEqualsPhysics : Bool
    qidCreatesScientificTruth : Bool
open ScienceBridgeRequirements public

scienceRequirements : ScienceBridgeRequirements
scienceRequirements =
  science-bridge-requirements true true true true true true false false

------------------------------------------------------------------------
-- Cross-funnel payoff.
-- Community and State reconnect the social/political branches; Science
-- reconnects natural, social, formal and applied branches.  These are thus
-- higher-alpha bridge repairs than adding arbitrary new leaf topics.
------------------------------------------------------------------------

record ParentBridgePayoff : Set where
  constructor parent-bridge-payoff
  field
    communityBridgePaysSocialBranches : Bool
    stateBridgePaysLawGovernancePoliticsBranches : Bool
    scienceBridgePaysNaturalSocialFormalAppliedBranches : Bool
    highFlowRepairPreferredToRandomLeafExpansion : Bool
    wikipediaParentDeterminesDashiOntology : Bool
open ParentBridgePayoff public

currentParentBridgePayoff : ParentBridgePayoff
currentParentBridgePayoff =
  parent-bridge-payoff true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CurrentEnParentIsTimeless : Set where
data CommunityMeansConsensus : Set where
data StateMeansGovernment : Set where
data ScientificKnowledgeMeansAllKnowledge : Set where

currentParentIsRevisionSensitive : CurrentEnParentIsTimeless → ⊥
currentParentIsRevisionSensitive ()

communityDoesNotMeanConsensus : CommunityMeansConsensus → ⊥
communityDoesNotMeanConsensus ()

stateDoesNotMeanGovernment : StateMeansGovernment → ⊥
stateDoesNotMeanGovernment ()

scienceDoesNotExhaustKnowledge : ScientificKnowledgeMeansAllKnowledge → ⊥
scienceDoesNotExhaustKnowledge ()

funnelBoundary : Funnel.IbrahimHighFlowCoverageBoundary
funnelBoundary = Funnel.canonicalIbrahimHighFlowCoverageBoundary
