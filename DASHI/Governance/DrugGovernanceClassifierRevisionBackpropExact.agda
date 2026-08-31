module DASHI.Governance.DrugGovernanceClassifierRevisionBackpropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical
import DASHI.Governance.DrugWarReflectingPoolFailureBoundaryExact as Failure

------------------------------------------------------------------------
-- CLASSIFIER REVISION BACKPROP
--
-- Historical classifier change is not exogenous magic.  New policy-outcome,
-- scientific/clinical, sovereignty and access evidence can create typed demands
-- to revise particular classification rules.  Reverse dependency closure then
-- reopens only route certificates whose proof path traverses the revised rule.
------------------------------------------------------------------------

data RevisionEvidenceKind : Set where
  goalFailureEvidence
  clinicalTherapeuticEvidence
  accessDisparityEvidence
  indigenousSovereigntyEvidence
  enforcementOutcomeEvidence
  historicalTargetingEvidence
  : RevisionEvidenceKind

data ClassifierRule : Set where
  punitiveStreetRule
  veteranClinicalExceptionRule
  indigenousCeremonialAuthorityRule
  commercialMedicalizationRule
  countercultureThreatClassificationRule
  : ClassifierRule

record ClassifierRevisionDemand : Set where
  constructor classifierRevisionDemand
  field
    evidenceKind : RevisionEvidenceKind
    targetRule : ClassifierRule
    currentVersion : Historical.ClassifierVersion
    proposedVersionReference : String
    evidenceReference : String
    comparisonReference : String
    mediationReference : String
    revisionAuthorised : Bool

open ClassifierRevisionDemand public

veteranTherapeuticRevisionDemand : ClassifierRevisionDemand
veteranTherapeuticRevisionDemand = classifierRevisionDemand
  clinicalTherapeuticEvidence
  veteranClinicalExceptionRule
  Historical.nixonEnforcementTreatmentVersion
  "candidate revision toward a later therapeutic/research classifier"
  "clinical and regulatory evidence for supervised psychedelic research/access"
  "compare same carrier/drug profile under historical classifier versions"
  "institutional mediation from evidence/regulatory change to route change still requires receipt"
  false

countercultureThreatRevisionDemand : ClassifierRevisionDemand
countercultureThreatRevisionDemand = classifierRevisionDemand
  historicalTargetingEvidence
  countercultureThreatClassificationRule
  Historical.nixonEnforcementTreatmentVersion
  "candidate historical re-audit of counterculture/antiwar threat classification"
  "archival policy, enforcement, campaign and retrospective motive evidence"
  "compare counterculture/antiwar carrier treatment with clinically legitimated later psychedelic carriers"
  "motive and classification mediation remain separate from observed association"
  false

------------------------------------------------------------------------
-- Exact reverse-dependency graph.
------------------------------------------------------------------------

data ClassifierArtifact : Set where
  veteranTherapeuticEvidenceArtifact
  countercultureHistoricalEvidenceArtifact
  sovereigntyEvidenceArtifact
  goalFailureEvidenceArtifact

  veteranClinicalRuleArtifact
  countercultureThreatRuleArtifact
  ceremonialAuthorityRuleArtifact
  punitiveStreetRuleArtifact

  veteranRouteCertificate
  countercultureRouteCertificate
  ceremonialRouteCertificate
  streetRouteCertificate

  carePunishmentConsumerCertificate
  historicalMeaningConsumerCertificate
  : ClassifierArtifact

data Depends : ClassifierArtifact → ClassifierArtifact → Set where
  veteranEvidenceToRule :
    Depends veteranTherapeuticEvidenceArtifact veteranClinicalRuleArtifact
  veteranRuleToRoute :
    Depends veteranClinicalRuleArtifact veteranRouteCertificate
  veteranRouteToConsumer :
    Depends veteranRouteCertificate carePunishmentConsumerCertificate

  countercultureEvidenceToRule :
    Depends countercultureHistoricalEvidenceArtifact countercultureThreatRuleArtifact
  countercultureRuleToRoute :
    Depends countercultureThreatRuleArtifact countercultureRouteCertificate
  countercultureRouteToMeaning :
    Depends countercultureRouteCertificate historicalMeaningConsumerCertificate

  sovereigntyEvidenceToRule :
    Depends sovereigntyEvidenceArtifact ceremonialAuthorityRuleArtifact
  ceremonialRuleToRoute :
    Depends ceremonialAuthorityRuleArtifact ceremonialRouteCertificate
  ceremonialRouteToConsumer :
    Depends ceremonialRouteCertificate carePunishmentConsumerCertificate

  failureEvidenceToStreetRule :
    Depends goalFailureEvidenceArtifact punitiveStreetRuleArtifact
  streetRuleToRoute :
    Depends punitiveStreetRuleArtifact streetRouteCertificate
  streetRouteToConsumer :
    Depends streetRouteCertificate carePunishmentConsumerCertificate

veteranEvidenceReopensVeteranRoute :
  Affected.ReopeningObligation
    Depends
    veteranTherapeuticEvidenceArtifact
    veteranRouteCertificate
veteranEvidenceReopensVeteranRoute =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation veteranEvidenceToRule)
    (Affected.oneEdgeCreatesReopeningObligation veteranRuleToRoute)

veteranEvidenceReopensCarePunishmentConsumer :
  Affected.ReopeningObligation
    Depends
    veteranTherapeuticEvidenceArtifact
    carePunishmentConsumerCertificate
veteranEvidenceReopensCarePunishmentConsumer =
  Affected.obligationsCompose
    veteranEvidenceReopensVeteranRoute
    (Affected.oneEdgeCreatesReopeningObligation veteranRouteToConsumer)

countercultureEvidenceReopensHistoricalMeaning :
  Affected.ReopeningObligation
    Depends
    countercultureHistoricalEvidenceArtifact
    historicalMeaningConsumerCertificate
countercultureEvidenceReopensHistoricalMeaning =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation countercultureEvidenceToRule)
      (Affected.oneEdgeCreatesReopeningObligation countercultureRuleToRoute))
    (Affected.oneEdgeCreatesReopeningObligation countercultureRouteToMeaning)

sovereigntyEvidenceReopensCarePunishmentConsumer :
  Affected.ReopeningObligation
    Depends
    sovereigntyEvidenceArtifact
    carePunishmentConsumerCertificate
sovereigntyEvidenceReopensCarePunishmentConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation sovereigntyEvidenceToRule)
      (Affected.oneEdgeCreatesReopeningObligation ceremonialRuleToRoute))
    (Affected.oneEdgeCreatesReopeningObligation ceremonialRouteToConsumer)

------------------------------------------------------------------------
-- Selectivity: a veteran clinical update does not directly depend into the
-- generic punitive-street rule or route merely because both live in drug policy.
------------------------------------------------------------------------

veteranEvidenceDoesNotDirectlyDependIntoStreetRule :
  Depends veteranTherapeuticEvidenceArtifact punitiveStreetRuleArtifact → ⊥
veteranEvidenceDoesNotDirectlyDependIntoStreetRule ()

veteranClinicalRuleDoesNotDirectlyDependIntoStreetRoute :
  Depends veteranClinicalRuleArtifact streetRouteCertificate → ⊥
veteranClinicalRuleDoesNotDirectlyDependIntoStreetRoute ()

countercultureEvidenceDoesNotDirectlyRewriteVeteranRule :
  Depends countercultureHistoricalEvidenceArtifact veteranClinicalRuleArtifact → ⊥
countercultureEvidenceDoesNotDirectlyRewriteVeteranRule ()

------------------------------------------------------------------------
-- Failure evidence itself is goal-relative and does not specify the replacement
-- classifier.  It may reopen a rule without proving which new rule is correct.
------------------------------------------------------------------------

failureBoundary : Failure.DrugWarReflectingPoolBoundary
failureBoundary = Failure.canonicalDrugWarReflectingPoolBoundary

data ReopenedRulePromotesReplacementRule : Set where

data ReopenedRulePromotesRefutation : Set where

reopeningDoesNotPromoteReplacement : ReopenedRulePromotesReplacementRule → ⊥
reopeningDoesNotPromoteReplacement ()

reopeningDoesNotPromoteRefutation : ReopenedRulePromotesRefutation → ⊥
reopeningDoesNotPromoteRefutation ()

record DrugGovernanceClassifierRevisionBoundary : Set where
  constructor drugGovernanceClassifierRevisionBoundary
  field
    evidenceCanReopenSpecificClassifierRule : Bool
    evidenceCanReopenSpecificClassifierRuleIsTrue :
      evidenceCanReopenSpecificClassifierRule ≡ true
    classifierRevisionPropagatesTransitivelyToAffectedConsumer : Bool
    classifierRevisionPropagatesTransitivelyToAffectedConsumerIsTrue :
      classifierRevisionPropagatesTransitivelyToAffectedConsumer ≡ true
    everyDrugPolicyEvidenceUpdateReopensEveryRoute : Bool
    everyDrugPolicyEvidenceUpdateReopensEveryRouteIsFalse :
      everyDrugPolicyEvidenceUpdateReopensEveryRoute ≡ false
    reopeningSelectsUniqueReplacementRule : Bool
    reopeningSelectsUniqueReplacementRuleIsFalse :
      reopeningSelectsUniqueReplacementRule ≡ false
    staleHistoricalClassifierEqualsRefutedHistoricalClassifier : Bool
    staleHistoricalClassifierEqualsRefutedHistoricalClassifierIsFalse :
      staleHistoricalClassifierEqualsRefutedHistoricalClassifier ≡ false

canonicalDrugGovernanceClassifierRevisionBoundary :
  DrugGovernanceClassifierRevisionBoundary
canonicalDrugGovernanceClassifierRevisionBoundary =
  drugGovernanceClassifierRevisionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
