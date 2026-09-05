module DASHI.Culture.MissingDeceasedDisruptionBenefitAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DisruptionBenefitHypothesisExact as D
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- Acquisition targets derived from the disruption-benefit hypotheses.
------------------------------------------------------------------------

data DisruptionAcquisitionTarget : Set where
  actorSpecificFusionExposure
  actorSpecificFissionExposure
  actorPerceptionOfTechnicalThreat
  rosterMatchedControls
  keyPersonReplaceabilityEvidence
  programmeDelayAfterLoss
  commonCapabilityAwareObserver
  historicalTechnicalSabotagePrecedent
  caseSpecificActorVisibility
  caseSpecificOperationalEvidence
  : DisruptionAcquisitionTarget

data TargetStatus : Set where
  targetPresent
  targetNotLocated
  targetKnownAbsent
  : TargetStatus

record DisruptionAcquisition : Set where
  constructor disruption-acquisition
  field
    target : DisruptionAcquisitionTarget
    status : TargetStatus
    preferredEvidence : String
    fallbackEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open DisruptionAcquisition public

stuxnetPrecedentAcquisition : DisruptionAcquisition
stuxnetPrecedentAcquisition = disruption-acquisition
  historicalTechnicalSabotagePrecedent
  targetPresent
  "contemporaneous reporting based on current/former officials and later official/declassified corroboration where available"
  "high-quality historical scholarship"
  "capability/willingness precedent for multidisciplinary state technical sabotage"
  "case attribution to any roster event"

fusionExposureAcquisition : DisruptionAcquisition
fusionExposureAcquisition = disruption-acquisition
  actorSpecificFusionExposure
  targetNotLocated
  "company/state revenue exposure, strategic planning, investment, lobbying, board/investor disclosures, energy-transition scenario modelling"
  "sector-level economic modelling with explicit actor mapping"
  "material economic/strategic benefit from delaying fusion for that actor"
  "motive, access, selection or perpetration"

threatPerceptionAcquisition : DisruptionAcquisition
threatPerceptionAcquisition = disruption-acquisition
  actorPerceptionOfTechnicalThreat
  targetNotLocated
  "contemporaneous internal/public strategy documents explicitly treating the relevant technology or programme as a threat/competitive risk"
  "authenticated statements, lobbying records, intelligence assessments, legal filings or correspondence"
  "actor-specific perceived benefit from disruption"
  "action against a person without separate evidence"

matchedControlsAcquisition : DisruptionAcquisition
matchedControlsAcquisition = disruption-acquisition
  rosterMatchedControls
  targetNotLocated
  "pre-registered matched peer sets by institution, field, seniority, visibility, sensitivity and geography/time"
  "public bibliometric/institutional datasets with blinded feature scoring"
  "roster enrichment or depletion for candidate features"
  "causal attribution"

replaceabilityAcquisition : DisruptionAcquisition
replaceabilityAcquisition = disruption-acquisition
  keyPersonReplaceabilityEvidence
  targetNotLocated
  "succession plans, role descriptions, unique facility qualifications, sole/rare technical responsibilities, programme testimony, replacement timelines"
  "credible institutional accounts of unique expertise and substitution difficulty"
  "low-replaceability/tacit-bottleneck feature"
  "intentional targeting"

programmeDelayAcquisition : DisruptionAcquisition
programmeDelayAcquisition = disruption-acquisition
  programmeDelayAfterLoss
  targetNotLocated
  "programme schedules before/after loss, milestones, staffing notices, project delays, reassignment records"
  "contemporaneous institutional statements"
  "actual disruption consequence"
  "who caused the loss"

capabilityAwareObserverAcquisition : DisruptionAcquisition
capabilityAwareObserverAcquisition = disruption-acquisition
  commonCapabilityAwareObserver
  targetNotLocated
  "portfolio review, technical-intelligence, programme-management, funding, advisory or contractor records jointly classifying multiple roster members by complementary capability"
  "shared conference/panel/review-board or technology-roadmap records"
  "one observer capable of recognizing cross-domain complementary value"
  "selection, harm or adversary"

caseVisibilityAcquisition : DisruptionAcquisition
caseVisibilityAcquisition = disruption-acquisition
  caseSpecificActorVisibility
  targetNotLocated
  "records showing a hypothesized actor/system actually tracked, contacted, reviewed, funded, surveilled, assessed or otherwise had visibility of a named roster person"
  "authenticated communications, official records, court records, declassified/FOIA records"
  "case-specific visibility/access premise"
  "perpetration without operational/forensic evidence"

operationalEvidenceAcquisition : DisruptionAcquisition
operationalEvidenceAcquisition = disruption-acquisition
  caseSpecificOperationalEvidence
  targetNotLocated
  "forensic, communications, travel, financial, operational, surveillance, access or witness evidence directly linking an actor to an event"
  "lawfully obtained authenticated primary evidence"
  "case attribution if independently sufficient and same-object"
  "nothing beyond its actual evidentiary scope"

------------------------------------------------------------------------
-- Hypotheses remain reopenable until evidence-bearing refutation/promotion.
------------------------------------------------------------------------

data DisruptionHypothesis : Set where
  fossilIncumbentBenefit
  foreignStrategicDenial
  rivalProgrammeBenefit
  capabilityAwareSelection
  tacitKnowledgeSelection
  : DisruptionHypothesis

disruptionSemantics : Forest.HypothesisSemantics DisruptionHypothesis
disruptionSemantics = Forest.hypothesisSemantics
  (λ _ → ⊥)
  (λ _ _ → ⊤)

fossilHypothesisDeferred :
  Forest.HypothesisTransition disruptionSemantics fossilIncumbentBenefit
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
fossilHypothesisDeferred = Forest.defer Forest.ambiguityUnresolved

strategicDenialDeferred :
  Forest.HypothesisTransition disruptionSemantics foreignStrategicDenial
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
strategicDenialDeferred = Forest.defer Forest.ambiguityUnresolved

failedAcquisitionDoesNotRefute :
  Forest.HypothesisTransition disruptionSemantics capabilityAwareSelection
    (Forest.reopenable Forest.ambiguityUnresolved) Forest.refuted → ⊥
failedAcquisitionDoesNotRefute = Forest.noDirectDormantRefutation

record DisruptionAcquisitionBoundary : Set where
  constructor disruption-acquisition-boundary
  field
    benefitSearchIsEvidenceGathering : Bool
    benefitSearchIsEvidenceGatheringIsTrue : benefitSearchIsEvidenceGathering ≡ true
    historicalPrecedentCreatesCaseAttribution : Bool
    historicalPrecedentCreatesCaseAttributionIsFalse : historicalPrecedentCreatesCaseAttribution ≡ false
    matchedControlFailureMayRefuteEnrichment : Bool
    matchedControlFailureMayRefuteEnrichmentIsTrue : matchedControlFailureMayRefuteEnrichment ≡ true
    actorExposureAloneCreatesMotive : Bool
    actorExposureAloneCreatesMotiveIsFalse : actorExposureAloneCreatesMotive ≡ false

canonicalDisruptionAcquisitionBoundary : DisruptionAcquisitionBoundary
canonicalDisruptionAcquisitionBoundary = disruption-acquisition-boundary
  true refl false refl true refl false refl
