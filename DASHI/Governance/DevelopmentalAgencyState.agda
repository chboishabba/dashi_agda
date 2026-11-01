module DASHI.Governance.DevelopmentalAgencyState where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.ConsentAgencyGovernanceCore as Consent
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Capability-relative developmental agency.
--
-- The formal carrier deliberately avoids hard-coded chronological stages.
-- Age can be an empirical predictor of capability, but normative conclusions
-- are indexed by the capabilities required for the proposition or decision.
------------------------------------------------------------------------

record DevelopmentalAgencySystem : Set₁ where
  field
    Subject : Set
    Domain : Set
    Stage : Set
    Capacity : Set

    interoceptiveCapacity : Subject → Domain → Stage → Capacity
    epistemicRevisionCapacity : Subject → Domain → Stage → Capacity
    volitionalCapacity : Subject → Domain → Stage → Capacity

    propositionalRepresentation : Subject → Domain → Stage → Set
    sourceMonitoring : Subject → Domain → Stage → Set
    counterfactualReasoning : Subject → Domain → Stage → Set
    evidenceEvaluation : Subject → Domain → Stage → Set
    refusalCapacity : Subject → Domain → Stage → Set

open DevelopmentalAgencySystem public

record CapabilityProfile
  (S : DevelopmentalAgencySystem)
  (subject : Subject S)
  (domain : Domain S)
  (stage : Stage S)
  : Set₁ where
  field
    canRepresentProposition : propositionalRepresentation S subject domain stage
    canMonitorSource : sourceMonitoring S subject domain stage
    canReasonCounterfactually : counterfactualReasoning S subject domain stage
    canEvaluateEvidence : evidenceEvaluation S subject domain stage
    canRefuse : refusalCapacity S subject domain stage

------------------------------------------------------------------------
-- Developmental influence is not itself a promotion to indoctrination.
------------------------------------------------------------------------

record AsymmetricInfluence
  (S : DevelopmentalAgencySystem) : Set₁ where
  field
    authority : Subject S
    learner : Subject S
    domain : Domain S
    stage : Stage S
    Influence : Set
    influence : Influence

data AsymmetryAloneEstablishesIndoctrination : Set where

asymmetryAloneDoesNotEstablishIndoctrination :
  AsymmetryAloneEstablishesIndoctrination → ⊥
asymmetryAloneDoesNotEstablishIndoctrination ()

------------------------------------------------------------------------
-- Consent is capability-relative rather than a single undifferentiated flag.
------------------------------------------------------------------------

record MeaningfulDevelopmentalConsent
  (S : DevelopmentalAgencySystem)
  (subject : Subject S)
  (domain : Domain S)
  (stage : Stage S)
  : Set₁ where
  field
    capabilityProfile : CapabilityProfile S subject domain stage
    informed : Set
    voluntary : Set
    refusalPreserved : Set
    withdrawalPreserved : Set

record DevelopmentalConsentBoundary : Set where
  constructor developmentalConsentBoundary
  field
    genericConsentGovernance : Consent.ConsentAgencyGovernance
    guardianPermissionEqualsChildCompetence : Bool
    assentEqualsMatureConsent : Bool
    chronologicalAgeAloneSettlesCompetence : Bool
    domainSpecificCapabilityRequired : Bool
    refusalAndWithdrawalRemainDistinct : Bool

canonicalDevelopmentalConsentBoundary : DevelopmentalConsentBoundary
canonicalDevelopmentalConsentBoundary =
  developmentalConsentBoundary
    Consent.canonicalConsentAgencyGovernance
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- Source-bound receipt.
------------------------------------------------------------------------

record DevelopmentalAgencyReceipt : Set where
  constructor developmentalAgencyReceipt
  field
    label : String
    sourceAtlas : List Sources.ScholarlySource
    asymmetryDoesNotPromoteIndoctrination : Bool
    ageDoesNotReplaceCapabilityAssessment : Bool
    beliefOriginDoesNotSettleBeliefTruth : Bool
    developmentalHistoryMayRemainRelevantToAutonomy : Bool

canonicalDevelopmentalAgencyReceipt : DevelopmentalAgencyReceipt
canonicalDevelopmentalAgencyReceipt =
  developmentalAgencyReceipt
    "capability-relative developmental agency"
    (Sources.epistemicTrustReview
      ∷ Sources.indoctrinationSpaceReasons
      ∷ Sources.rewardProcessingModel
      ∷ [])
    true true true true
