module DASHI.Governance.BoloBoloSocialEcologyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SocialEcologyHierarchyProjectionBoundaryExact as Hierarchy
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Observer
import DASHI.Governance.BoloBoloOccupyTranscriptSourceBoundaryExact as Transcript
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence
import DASHI.Governance.RevolutionaryPracticeBraid as Practice

------------------------------------------------------------------------
-- Cross-pollination boundary.
--
-- The attached transcript reports the author's encounter with social ecology
-- and their own assessment of it.  Existing DASHI social-ecology modules are
-- separately sourced to Bookchin/King/etc.  This module keeps those provenance
-- chains distinct while reusing their theorem patterns as safeguards.
------------------------------------------------------------------------

sameCarrierDoesNotDetermineSocialRank :
  Hierarchy.rankedRegime Ternary.code2 Ternary.code1
  ≡ Hierarchy.nonrankingRegime Ternary.code2 Ternary.code1
  → ⊥
sameCarrierDoesNotDetermineSocialRank =
  Hierarchy.sameCarrierDifferentRanking

nominalLiberatoryLabelDoesNotRecoverAffordance :
  INF.FactorsThrough
    Observer.nominalLiberatoryObserver
    Observer.realizedRemain
  → ⊥
nominalLiberatoryLabelDoesNotRecoverAffordance =
  Observer.nominalLiberatoryLabelCannotRecoverRealizedAffordance

repoFederationWithoutAbsorptionAnalogue : Practice.PrefigurativePractice
repoFederationWithoutAbsorptionAnalogue =
  Practice.federationWithoutAbsorptionPractice

localityStillNeedsExplicitSubsidiarity :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  ∀ {issue community} →
  Base.scopeOf governance issue ≡ Base.localTo community →
  Σ Agent (λ agent → ¬ Base.memberOf governance agent community) →
  ¬ Incidence.GloballyCoupledIssue governance issue
localityStillNeedsExplicitSubsidiarity =
  Incidence.localIssueWithOutsiderNotGloballyCoupled

record BoloBoloSocialEcologyCrossPollinationBoundary : Set where
  constructor boloBoloSocialEcologyCrossPollinationBoundary
  field
    transcriptSocialEcologyMentionCreatesBookchinEndorsement : Bool
    transcriptAuthorAssessmentEqualsBookchinTheory : Bool
    federatedLocalityProvesHierarchyAbsent : Bool
    decentralisedStructureDeterminesNonDomination : Bool
    observerRegimeSelectsPoliticalAuthority : Bool
    repoFederationPatternAttributedToTranscript : Bool
    transcriptSuppliesBoloInstitutionalDesign : Bool
    crossPollinationRetainsSourceSeparation : Bool

open BoloBoloSocialEcologyCrossPollinationBoundary public

canonicalBoloBoloSocialEcologyCrossPollinationBoundary :
  BoloBoloSocialEcologyCrossPollinationBoundary
canonicalBoloBoloSocialEcologyCrossPollinationBoundary =
  boloBoloSocialEcologyCrossPollinationBoundary
    false
    false
    false
    false
    false
    false
    false
    true

canonicalBoloBoloSocialEcologyCrossPollinationReceipt :
  GenericReceipt.GenericReceipt
canonicalBoloBoloSocialEcologyCrossPollinationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Bolo Bolo / social-ecology federation cross-pollination"
    "DASHI.Governance.BoloBoloSocialEcologyCrossPollinationExact"
    "canonicalBoloBoloSocialEcologyCrossPollinationBoundary"
    "reuses existing hierarchy-non-determination and observer/affordance non-factorability safeguards alongside the federated subsidiarity locality theorem and the repo-internal federation-without-absorption practice analogue"
    "the transcript's social-ecology mention is not treated as Bookchin endorsement, federation does not prove hierarchy absent or non-domination, and the repo practice analogue is not attributed to the attached clip"
    "agda -i . DASHI/Governance/BoloBoloSocialEcologyCrossPollinationRegression.agda"
