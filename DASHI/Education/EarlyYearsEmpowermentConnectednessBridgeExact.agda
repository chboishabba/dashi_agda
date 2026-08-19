module DASHI.Education.EarlyYearsEmpowermentConnectednessBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementCore as Observer
import DASHI.Education.CapabilityRecognitionExact as Recognition
import DASHI.Education.CommunityConnectednessTopologyExact as Connectedness
import DASHI.Education.EarlyLearningCounterfactualHeterogeneityExact as Counterfactual
import DASHI.Education.EarlyLearningMultiOutcomeVectorExact as Outcomes
import DASHI.Education.EarlyLearningSituatedPolicyRoutingSafetyExact as Routing
import DASHI.Education.EarlyYearsEmpowermentConnectednessSourceRegistry as Sources
import DASHI.Education.EarlyYearsStakeholderCoverageExact as Coverage
import DASHI.Education.SituatedRelationalLearningAffordanceExact as Affordance
import DASHI.Semantics.SIOSemanticSurfaceBridge as SIO

------------------------------------------------------------------------
-- EARLY-YEARS EMPOWERMENT + CONNECTEDNESS BRIDGE
--
-- This is a thin specialization over the #582 convergence stack. It does not
-- define empowerment as a scalar state. The exact structural object is a
-- situated transition certificate: pre-existing capability remains present,
-- a reachable/recognisable route opens, contestability is retained, relational
-- effectiveness is witnessed, no authority is manufactured, and any empirical
-- claim remains bounded by its active stakeholder evidence axes.
------------------------------------------------------------------------

record EmpowermentPreconditions : Set where
  constructor empowermentPreconditions
  field
    actorCapabilityRepresented : Bool
    realChoiceRoutePresent : Bool
    participationNonCoercive : Bool
    actorKnowledgeAdmissible : Bool
    authorityBoundaryExplicit : Bool
    provenanceRetained : Bool
    opportunityActuallyReachable : Bool
    evaluationNotReducedToCompliance : Bool
    measurementHorizonDeclared : Bool
    counterfactualFrameDeclaredWhenCausal : Bool

open EmpowermentPreconditions public

record EmpowermentPostconditions : Set where
  constructor empowermentPostconditions
  field
    preExistingCapabilityPreserved : Bool
    atLeastOneReachableActionOpened : Bool
    capabilityRecognitionOpened : Bool
    effectiveConnectionWitnessed : Bool
    actorDeclineRoutePreserved : Bool
    noInstitutionalAuthorityManufactured : Bool
    outcomeAxisRemainsDeclared : Bool
    claimScopeRemainsStakeholderIndexed : Bool

open EmpowermentPostconditions public

canonicalPreconditions : EmpowermentPreconditions
canonicalPreconditions =
  empowermentPreconditions true true true true true true true true true true

canonicalPostconditions : EmpowermentPostconditions
canonicalPostconditions =
  empowermentPostconditions true true true true true true true true

------------------------------------------------------------------------
-- Exact structural certificate.
------------------------------------------------------------------------

record CapabilityExpandingWithoutDomination : Set where
  constructor capabilityExpandingWithoutDomination
  field
    beforeRecognition : Recognition.CapabilityRecognitionState
    afterRecognition : Recognition.CapabilityRecognitionState
    recognitionTransition :
      Recognition.StrengthBasedRecognitionTransition beforeRecognition afterRecognition
    connectionAfter : Connectedness.CommunityConnectionState
    connectionIsEffective : Connectedness.effectiveConnection connectionAfter ≡ true
    noConnectionAuthorityPromotion : Connectedness.currentAuthority connectionAfter ≡ false
    preconditions : EmpowermentPreconditions
    postconditions : EmpowermentPostconditions
    receipt : String

open CapabilityExpandingWithoutDomination public

canonicalCapabilityExpandingWithoutDomination : CapabilityExpandingWithoutDomination
canonicalCapabilityExpandingWithoutDomination =
  capabilityExpandingWithoutDomination
    Recognition.latentUnrecognised
    Recognition.reachableRecognised
    Recognition.mulchingShapeTransition
    Connectedness.effectivePeerConnection
    refl refl
    canonicalPreconditions
    canonicalPostconditions
    "finite strength-based witness: existing capability becomes reachable, legible and recognised through an effective peer/community route while decline and non-authority boundaries are retained"

------------------------------------------------------------------------
-- Existing upstream invariants are carried into the bridge, not re-proved.
------------------------------------------------------------------------

reachableContestableAffordanceGate : Affordance.ReachableContestableAffordanceGate
reachableContestableAffordanceGate = Affordance.canonicalReachableContestableAffordanceGate

professionalPilotClaimBoundary : Coverage.StakeholderCoverageBoundary
professionalPilotClaimBoundary = Coverage.canonicalStakeholderCoverageBoundary

capabilityRecognitionBoundary : Recognition.CapabilityRecognitionBoundary
capabilityRecognitionBoundary = Recognition.canonicalCapabilityRecognitionBoundary

communityConnectednessBoundary : Connectedness.CommunityConnectednessBoundary
communityConnectednessBoundary = Connectedness.canonicalCommunityConnectednessBoundary

peerCatalystBoundary : Connectedness.PeerCatalystBoundary
peerCatalystBoundary = Connectedness.canonicalPeerCatalystBoundary

------------------------------------------------------------------------
-- Observer family, causal heterogeneity, outcome-vector, policy-routing and SIO
-- semantics are deliberately imported as theorem owners. Product observation
-- does not become semantic/evidential pooling permission; a rights surface does
-- not become a complete router; an intervention label does not become its
-- situated effect; one outcome axis does not become the whole outcome vector.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- No-promotion permissions.
------------------------------------------------------------------------

data ParticipationEqualsEmpowermentPermission : Set where
data ComplianceEqualsAgencyPermission : Set where
data ProfessionalPilotEqualsFamilyExperiencePermission : Set where
data CapabilityExpansionEqualsUniversalEmpowermentPermission : Set where
data PeerCatalystEqualsAuthorityPermission : Set where
data EffectiveConnectionEqualsGoodOutcomePermission : Set where

participationCannotAutoPromoteToEmpowerment :
  ParticipationEqualsEmpowermentPermission → ⊥
participationCannotAutoPromoteToEmpowerment ()

complianceCannotAutoPromoteToAgency : ComplianceEqualsAgencyPermission → ⊥
complianceCannotAutoPromoteToAgency ()

professionalPilotCannotAutoPromoteToFamilyExperience :
  ProfessionalPilotEqualsFamilyExperiencePermission → ⊥
professionalPilotCannotAutoPromoteToFamilyExperience ()

capabilityExpansionCannotAutoPromoteToUniversalEmpowerment :
  CapabilityExpansionEqualsUniversalEmpowermentPermission → ⊥
capabilityExpansionCannotAutoPromoteToUniversalEmpowerment ()

peerCatalystCannotAutoPromoteToAuthority : PeerCatalystEqualsAuthorityPermission → ⊥
peerCatalystCannotAutoPromoteToAuthority ()

effectiveConnectionCannotAutoPromoteToGoodOutcome :
  EffectiveConnectionEqualsGoodOutcomePermission → ⊥
effectiveConnectionCannotAutoPromoteToGoodOutcome ()

------------------------------------------------------------------------
-- Source-facing handles. Metadata is not proof authority.
------------------------------------------------------------------------

earlyYearsStrategySource : Sources.EmpowermentConnectednessReference
earlyYearsStrategySource = Sources.earlyYearsStrategy2024

qualityArea6Source : Sources.EmpowermentConnectednessReference
qualityArea6Source = Sources.qualityArea6

brownKimberAgencySource : Sources.EmpowermentConnectednessReference
brownKimberAgencySource = Sources.brownKimber2026

------------------------------------------------------------------------
-- Compact invariant bundle.
------------------------------------------------------------------------

record EmpowermentConnectednessInvariant : Set where
  constructor empowermentConnectednessInvariant
  field
    observerSurfaceEqualsWholeSystem : Bool
    missingStakeholderInvalidatesEveryClaim : Bool
    missingActiveStakeholderBlocksDirectClaim : Bool
    participationImpliesEmpowerment : Bool
    nonRecognitionImpliesNoCapability : Bool
    formalConnectionImpliesEffectiveConnection : Bool
    effectiveConnectionImpliesAuthority : Bool
    familyAgencyImpliesParentalSovereignty : Bool
    rightsSurfaceIsCompleteRouter : Bool
    capabilityExpansionRequiresSemanticPromotionWitness : Bool
    causalClaimRequiresCounterfactualAndOutcomeDiscipline : Bool

open EmpowermentConnectednessInvariant public

canonicalEmpowermentConnectednessInvariant : EmpowermentConnectednessInvariant
canonicalEmpowermentConnectednessInvariant =
  empowermentConnectednessInvariant
    false false true false false false false false false true true

empowermentConnectednessReading : String
empowermentConnectednessReading =
  "The exact primitive is capability expansion without domination, not a scalar empowered/not-empowered label. A bounded claim declares its stakeholder evidence axes; pre-existing capability may become reachable, legible and recognised through effective reciprocal topology; participation, professional observation, peer influence and formal connection do not self-promote to empowerment, family experience, authority or good outcome. Causal and whole-policy claims remain counterfactual-, outcome-, horizon- and provenance-indexed."
