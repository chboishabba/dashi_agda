module DASHI.Culture.MissingDeceasedCapabilitySelectorAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- Acquisition targets for the stronger question:
-- which observer could both SEE the person and RECOGNISE the capability value
-- of that person's specialised work?
------------------------------------------------------------------------

data CapabilitySelectorTarget : Set where
  technicalPortfolioReview
  strategicTechnologyRoadmap
  programmeDependencyReview
  keyPersonRiskRegister
  technicalIntelligenceAssessment
  crossProgrammeAdvisoryPanel
  technologyTransferOrLicensingReview
  fusionEnergyCompetitiveThreatAssessment
  : CapabilitySelectorTarget

data TargetStatus : Set where
  targetPresent
  targetNotLocated
  targetKnownAbsent
  : TargetStatus

record CapabilitySelectorAcquisition : Set where
  constructor capability-selector-acquisition
  field
    target : CapabilitySelectorTarget
    status : TargetStatus
    soughtObserver : String
    preferredEvidence : String
    whatItWouldEstablish : String
    whatItWouldNotEstablish : String

open CapabilitySelectorAcquisition public

portfolioReviewAcquisition : CapabilitySelectorAcquisition
portfolioReviewAcquisition = capability-selector-acquisition
  technicalPortfolioReview
  targetNotLocated
  "programme/funding/technical portfolio observer spanning complementary roster work"
  "portfolio reviews, technology roadmaps, programme dependency matrices, funding prioritisation records or official technical capability assessments naming the person/work"
  "an observer had both visibility and a capability-indexed reason to regard the specialist as salient"
  "targeting, hostility, disruption intent or case attribution"

keyPersonRiskAcquisition : CapabilitySelectorAcquisition
keyPersonRiskAcquisition = capability-selector-acquisition
  keyPersonRiskRegister
  targetNotLocated
  "organisation or programme observer tracking substitution difficulty / unique expertise"
  "succession plans, critical-skills matrices, key-person risk registers, sole-source expertise records, staffing risk reviews or authenticated management testimony"
  "the person's replaceability/tacit knowledge was explicitly visible to an observer"
  "that the observer wanted the person removed"

technicalIntelligenceAcquisition : CapabilitySelectorAcquisition
technicalIntelligenceAcquisition = capability-selector-acquisition
  technicalIntelligenceAssessment
  targetNotLocated
  "state technical-intelligence observer capable of ranking foreign/domestic specialists by strategic capability contribution"
  "declassified technical-intelligence assessments, official collection requirements, judicial/congressional exhibits or authenticated government records naming the specialist/work"
  "capability-aware state visibility"
  "selection for harm or operational involvement"

fusionThreatAcquisition : CapabilitySelectorAcquisition
fusionThreatAcquisition = capability-selector-acquisition
  fusionEnergyCompetitiveThreatAssessment
  targetNotLocated
  "energy incumbent, state, investor or strategic planner treating commercial fusion as material competitive substitution"
  "contemporaneous strategy, investor, lobbying, market-scenario, risk-factor or internal planning documents that explicitly characterize fusion as a material threat and identify relevant research bottlenecks/personnel if available"
  "actor-specific perception of fusion as a competitive/economic threat"
  "visibility of Loureiro specifically unless the same evidence names or otherwise identifies him"

crossProgrammePanelAcquisition : CapabilitySelectorAcquisition
crossProgrammePanelAcquisition = capability-selector-acquisition
  crossProgrammeAdvisoryPanel
  targetNotLocated
  "advisory/review body spanning otherwise separate technical programmes"
  "conference panels, review boards, advisory committees, standards groups, workshops, roadmapping exercises or peer-review rosters"
  "cross-domain capability awareness without requiring victim-victim collaboration"
  "harm, adversary or covert selection"

------------------------------------------------------------------------
-- Reopenable hypothesis semantics.
------------------------------------------------------------------------

data CapabilitySelectorHypothesis : Set where
  portfolioCapabilitySelector
  keyPersonSelector
  technicalIntelligenceSelector
  fusionThreatSelector
  advisoryNetworkSelector
  : CapabilitySelectorHypothesis

selectorSemantics : Forest.HypothesisSemantics CapabilitySelectorHypothesis
selectorSemantics = Forest.hypothesisSemantics
  (λ _ → ⊥)
  (λ _ _ → ⊤)

portfolioSelectorDeferred :
  Forest.HypothesisTransition selectorSemantics portfolioCapabilitySelector
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
portfolioSelectorDeferred = Forest.defer Forest.ambiguityUnresolved

technicalIntelligenceDeferred :
  Forest.HypothesisTransition selectorSemantics technicalIntelligenceSelector
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
technicalIntelligenceDeferred = Forest.defer Forest.ambiguityUnresolved

record CapabilitySelectorAcquisitionBoundary : Set where
  constructor capability-selector-acquisition-boundary
  field
    publicVisibilityAloneEstablishesCapabilityAwareness : Bool
    publicVisibilityAloneEstablishesCapabilityAwarenessIsFalse :
      publicVisibilityAloneEstablishesCapabilityAwareness ≡ false

    capabilityAwarenessRequiresVictimVictimContact : Bool
    capabilityAwarenessRequiresVictimVictimContactIsFalse :
      capabilityAwarenessRequiresVictimVictimContact ≡ false

    keyPersonRiskEvidenceImpliesHostility : Bool
    keyPersonRiskEvidenceImpliesHostilityIsFalse :
      keyPersonRiskEvidenceImpliesHostility ≡ false

    actorThreatAssessmentImpliesAction : Bool
    actorThreatAssessmentImpliesActionIsFalse :
      actorThreatAssessmentImpliesAction ≡ false

canonicalCapabilitySelectorAcquisitionBoundary : CapabilitySelectorAcquisitionBoundary
canonicalCapabilitySelectorAcquisitionBoundary = capability-selector-acquisition-boundary
  false refl
  false refl
  false refl
  false refl
