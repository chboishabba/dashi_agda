module DASHI.Culture.CohnInstitutionalNormReasonablenessEvidenceCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.InstitutionalNormSituatedReasonablenessBridgeExact as NormReason
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverSituatedReasonablenessExact as Situated
import DASHI.Culture.CohnDiscursiveAdmissibilityNaturalisationExact as CohnDiscursive
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as CohnSources
import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as Expert
import DASHI.Law.SensibLawLegalReasonablenessExact as Legal

------------------------------------------------------------------------
-- COHN × INSTITUTIONAL NORM × LEGAL REASONABLENESS × EVIDENCE ADEQUACY
--
-- Thin cross-domain bridge.  Cohn remains a source-bounded discourse fixture;
-- Cohn is not imported as legal authority and does not author the finite DASHI
-- collision below.  The legal sources remain legal-source receipts rather than
-- proof of the generic information-theoretic theorem.
--
-- Core separation:
--
--   institutionally normal
--     != legally reasonable under a declared legal index
--     != evidentially / consumer adequate for every downstream query.
------------------------------------------------------------------------

parentNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

parentNormReasonablenessBoundary : NormReason.InstitutionalNormReasonablenessBoundary
parentNormReasonablenessBoundary =
  NormReason.canonicalInstitutionalNormReasonablenessBoundary

parentSituatedReasonablenessBoundary : Situated.SituatedReasonablenessBoundary
parentSituatedReasonablenessBoundary = Situated.canonicalSituatedReasonablenessBoundary

parentLegalReasonablenessBoundary : Legal.LegalReasonablenessBoundary
parentLegalReasonablenessBoundary = Legal.canonicalLegalReasonablenessBoundary

parentExpertSituatedObserverBoundary : Expert.ExpertSituatedObserverBoundary
parentExpertSituatedObserverBoundary = Expert.canonicalExpertSituatedObserverBoundary

parentCohnDiscursiveBoundary : CohnDiscursive.DiscursiveAdmissibilityBoundary
parentCohnDiscursiveBoundary =
  CohnDiscursive.canonicalDiscursiveAdmissibilityBoundary

------------------------------------------------------------------------
-- Finite DASHI composition witness.
------------------------------------------------------------------------

data InstitutionalLegalEvidenceState : Set where
  conventionalReasonableAdequate : InstitutionalLegalEvidenceState
  conventionalUnreasonableInadequate : InstitutionalLegalEvidenceState
  conventionalReasonableInadequate : InstitutionalLegalEvidenceState


data InstitutionalNormalityCode : Set where
  sameInstitutionalConvention : InstitutionalNormalityCode


data LegalReasonablenessCode : Set where
  withinLegalReasonablenessRange : LegalReasonablenessCode
  outsideLegalReasonablenessRange : LegalReasonablenessCode


data EvidenceAdequacyCode : Set where
  evidenceAdequateForConsumer : EvidenceAdequacyCode
  evidenceInadequateForConsumer : EvidenceAdequacyCode


data ProductionHistoryCode : Set where
  broadProductionHistory : ProductionHistoryCode
  narrowProductionHistory : ProductionHistoryCode


data EvidenceProvenanceCode : Set where
  independentSituatedEvidence : EvidenceProvenanceCode
  conventionDominatedEvidence : EvidenceProvenanceCode

institutionalNormalityProjection :
  InstitutionalLegalEvidenceState → InstitutionalNormalityCode
institutionalNormalityProjection _ = sameInstitutionalConvention

legalReasonablenessProjection :
  InstitutionalLegalEvidenceState → LegalReasonablenessCode
legalReasonablenessProjection conventionalReasonableAdequate =
  withinLegalReasonablenessRange
legalReasonablenessProjection conventionalUnreasonableInadequate =
  outsideLegalReasonablenessRange
legalReasonablenessProjection conventionalReasonableInadequate =
  withinLegalReasonablenessRange

evidenceAdequacyProjection :
  InstitutionalLegalEvidenceState → EvidenceAdequacyCode
evidenceAdequacyProjection conventionalReasonableAdequate =
  evidenceAdequateForConsumer
evidenceAdequacyProjection conventionalUnreasonableInadequate =
  evidenceInadequateForConsumer
evidenceAdequacyProjection conventionalReasonableInadequate =
  evidenceInadequateForConsumer

productionHistoryProjection :
  InstitutionalLegalEvidenceState → ProductionHistoryCode
productionHistoryProjection conventionalReasonableAdequate = broadProductionHistory
productionHistoryProjection conventionalUnreasonableInadequate = narrowProductionHistory
productionHistoryProjection conventionalReasonableInadequate = narrowProductionHistory

evidenceProvenanceProjection :
  InstitutionalLegalEvidenceState → EvidenceProvenanceCode
evidenceProvenanceProjection conventionalReasonableAdequate = independentSituatedEvidence
evidenceProvenanceProjection conventionalUnreasonableInadequate = conventionDominatedEvidence
evidenceProvenanceProjection conventionalReasonableInadequate = conventionDominatedEvidence

------------------------------------------------------------------------
-- Institutional normality != legal reasonableness.
------------------------------------------------------------------------

normalityReasonablenessCollision :
  INF.NonFactorabilityWitness
    institutionalNormalityProjection
    legalReasonablenessProjection
normalityReasonablenessCollision =
  INF.nonFactorabilityWitness
    conventionalReasonableAdequate
    conventionalUnreasonableInadequate
    refl
    (λ ())

institutionalNormalityDoesNotDetermineLegalReasonableness :
  INF.FactorsThrough
    institutionalNormalityProjection
    legalReasonablenessProjection → ⊥
institutionalNormalityDoesNotDetermineLegalReasonableness =
  INF.witnessRulesOutEveryFlatFactorisation normalityReasonablenessCollision

------------------------------------------------------------------------
-- Legal reasonableness != evidence / consumer adequacy.
------------------------------------------------------------------------

reasonablenessAdequacyCollision :
  INF.NonFactorabilityWitness
    legalReasonablenessProjection
    evidenceAdequacyProjection
reasonablenessAdequacyCollision =
  INF.nonFactorabilityWitness
    conventionalReasonableAdequate
    conventionalReasonableInadequate
    refl
    (λ ())

legalReasonablenessDoesNotDetermineEvidenceAdequacy :
  INF.FactorsThrough
    legalReasonablenessProjection
    evidenceAdequacyProjection → ⊥
legalReasonablenessDoesNotDetermineEvidenceAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation reasonablenessAdequacyCollision

normalityAdequacyCollision :
  INF.NonFactorabilityWitness
    institutionalNormalityProjection
    evidenceAdequacyProjection
normalityAdequacyCollision =
  INF.nonFactorabilityWitness
    conventionalReasonableAdequate
    conventionalReasonableInadequate
    refl
    (λ ())

institutionalNormalityDoesNotDetermineEvidenceAdequacy :
  INF.FactorsThrough
    institutionalNormalityProjection
    evidenceAdequacyProjection → ⊥
institutionalNormalityDoesNotDetermineEvidenceAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation normalityAdequacyCollision

------------------------------------------------------------------------
-- Constructive audit refinement.
------------------------------------------------------------------------

record EnrichedLegalEvidenceAudit : Set where
  constructor mkEnrichedLegalEvidenceAudit
  field
    normality : InstitutionalNormalityCode
    legalReasonableness : LegalReasonablenessCode
    evidenceAdequacy : EvidenceAdequacyCode
    productionHistory : ProductionHistoryCode
    evidenceProvenance : EvidenceProvenanceCode

open EnrichedLegalEvidenceAudit public

enrichedLegalEvidenceAudit :
  InstitutionalLegalEvidenceState → EnrichedLegalEvidenceAudit
enrichedLegalEvidenceAudit state =
  mkEnrichedLegalEvidenceAudit
    (institutionalNormalityProjection state)
    (legalReasonablenessProjection state)
    (evidenceAdequacyProjection state)
    (productionHistoryProjection state)
    (evidenceProvenanceProjection state)

evidenceAdequacyFactorsThroughEnrichedAudit :
  INF.FactorsThrough enrichedLegalEvidenceAudit evidenceAdequacyProjection
evidenceAdequacyFactorsThroughEnrichedAudit =
  INF.factorsThrough
    evidenceAdequacy
    (λ { conventionalReasonableAdequate → refl
       ; conventionalUnreasonableInadequate → refl
       ; conventionalReasonableInadequate → refl })

------------------------------------------------------------------------
-- Direct parent theorem reuse.
------------------------------------------------------------------------

ProductionHistoryThroughDeclaredStandard : Set₁
ProductionHistoryThroughDeclaredStandard =
  NormReason.ProductionHistoryThroughDeclaredStandard

productionHistoryDoesNotFactorThroughDeclaredStandard :
  ProductionHistoryThroughDeclaredStandard → ⊥
productionHistoryDoesNotFactorThroughDeclaredStandard =
  NormReason.productionHistoryDoesNotFactorThroughDeclaredStandard

institutionalConventionNotAutomaticallyReasonable :
  Situated.institutionalConventionAutomaticallyReasonable
    Situated.canonicalSituatedReasonablenessBoundary ≡ false
institutionalConventionNotAutomaticallyReasonable = refl

socialConformityNotAutomaticallyCredible :
  Expert.socialNormConformityAutomaticallyCredibility
    Expert.canonicalExpertSituatedObserverBoundary ≡ false
socialConformityNotAutomaticallyCredible = refl

legalReasonablenessRemainsIndexed : Situated.ReasonablenessIndex
legalReasonablenessRemainsIndexed = Legal.legalReasonablenessIndexExample

------------------------------------------------------------------------
-- Attribution / authority boundary.
------------------------------------------------------------------------

cohnCitationStillDoesNotCreateAuthority :
  Source.citationCreatesAuthority CohnSources.cohnSexAndDeath ≡ false
cohnCitationStillDoesNotCreateAuthority = refl

record CohnInstitutionalLegalEvidenceBoundary : Set where
  constructor cohnInstitutionalLegalEvidenceBoundary
  field
    institutionalNormalityImpliesLegalReasonableness : Bool
    institutionalNormalityImpliesLegalReasonablenessIsFalse :
      institutionalNormalityImpliesLegalReasonableness ≡ false
    legalReasonablenessImpliesUniversalEvidenceAdequacy : Bool
    legalReasonablenessImpliesUniversalEvidenceAdequacyIsFalse :
      legalReasonablenessImpliesUniversalEvidenceAdequacy ≡ false
    institutionalNormalityImpliesEvidenceAdequacy : Bool
    institutionalNormalityImpliesEvidenceAdequacyIsFalse :
      institutionalNormalityImpliesEvidenceAdequacy ≡ false
    declaredStandardRevealsProductionHistory : Bool
    declaredStandardRevealsProductionHistoryIsFalse :
      declaredStandardRevealsProductionHistory ≡ false
    socialConformityEstablishesCredibility : Bool
    socialConformityEstablishesCredibilityIsFalse :
      socialConformityEstablishesCredibility ≡ false
    cohnCitationCreatesLegalAuthority : Bool
    cohnCitationCreatesLegalAuthorityIsFalse :
      cohnCitationCreatesLegalAuthority ≡ false
    discourseAnalysisDeterminesLegalOutcome : Bool
    discourseAnalysisDeterminesLegalOutcomeIsFalse :
      discourseAnalysisDeterminesLegalOutcome ≡ false
    evidenceAdequacyCreatesLegalAuthority : Bool
    evidenceAdequacyCreatesLegalAuthorityIsFalse :
      evidenceAdequacyCreatesLegalAuthority ≡ false
    richerAuditCarrierCanRepairFiniteAdequacyQuery : Bool
    richerAuditCarrierCanRepairFiniteAdequacyQueryIsTrue :
      richerAuditCarrierCanRepairFiniteAdequacyQuery ≡ true

open CohnInstitutionalLegalEvidenceBoundary public

canonicalCohnInstitutionalLegalEvidenceBoundary :
  CohnInstitutionalLegalEvidenceBoundary
canonicalCohnInstitutionalLegalEvidenceBoundary =
  cohnInstitutionalLegalEvidenceBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
