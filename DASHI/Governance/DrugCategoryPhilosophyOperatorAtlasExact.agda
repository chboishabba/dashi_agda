module DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Culture.WittgensteinUsePracticeSourceBridgeExact as Wittgenstein
import DASHI.Reasoning.PNFZizekOperator as Zizek
import DASHI.Reasoning.LacanZizekIdeologyBridge as LacanZizek
import DASHI.Culture.IntersectionalPowerValueFolkModelBoundary as Philosophy
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Critical

------------------------------------------------------------------------
-- PHILOSOPHY OPERATOR ATLAS OVER CONTESTED DRUG CATEGORIES
--
-- Philosophers supply typed audit questions, not a master ontology.  Source
-- propositions, interpretive bridges, reusable theorem patterns and empirical
-- claims remain distinct layers.
------------------------------------------------------------------------

data DrugCategoryAudit : Set where
  wittgensteinUseAudit
  zizekClosureFantasyAudit
  foucaultPowerClassificationAudit
  marxMaterialInterestAudit
  nietzscheValuationFormationAudit
  spinozaPowerToActAudit
  kantNonInstrumentalisationAudit
  levinasOtherExceedsChartAudit
  derridaNoFinalClosureAudit
  feministSubjectPositionAudit
  intersectionalAxisAudit
  : DrugCategoryAudit

data AuditQuestion : DrugCategoryAudit → Set where
  askUsePractice : AuditQuestion wittgensteinUseAudit
  askMasterPredicateAndExcludedResidual : AuditQuestion zizekClosureFantasyAudit
  askInstitutionalPowerProduction : AuditQuestion foucaultPowerClassificationAudit
  askMaterialOwnershipBenefit : AuditQuestion marxMaterialInterestAudit
  askValueProductionHistory : AuditQuestion nietzscheValuationFormationAudit
  askCapacityToAct : AuditQuestion spinozaPowerToActAudit
  askNonInstrumentalisation : AuditQuestion kantNonInstrumentalisationAudit
  askWhatExceedsRepresentation : AuditQuestion levinasOtherExceedsChartAudit
  askClosureResidual : AuditQuestion derridaNoFinalClosureAudit
  askOriginatingSubjectPosition : AuditQuestion feministSubjectPositionAudit
  askIntersectingAxes : AuditQuestion intersectionalAxisAudit

record CategoryAuditReceipt
    (assertion : Atlas.CategoryAssertion)
    (audit : DrugCategoryAudit) : Set where
  constructor categoryAuditReceipt
  field
    question : AuditQuestion audit
    observationReference : String
    interpretationReference : String
    empiricalEvidenceReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CategoryAuditReceipt public

------------------------------------------------------------------------
-- Wittgenstein operator: same word/category does not settle use or form of life.
------------------------------------------------------------------------

wittgensteinBoundary : Wittgenstein.WittgensteinUsePracticeBoundary
wittgensteinBoundary = Wittgenstein.canonicalWittgensteinUsePracticeBoundary

samePatientWordStillDoesNotRecoverPractice :
  (recover : Atlas.PatientWord → Atlas.PatientPracticeCode) →
  ((state : Atlas.PatientUseState) →
    recover (Atlas.patientWord state) ≡ Atlas.patientPractice state) → ⊥
samePatientWordStillDoesNotRecoverPractice recover recovers =
  Atlas.samePatientWordCannotRecoverPractice
    (record { factor = recover ; commutes = recovers })

------------------------------------------------------------------------
-- Zizek operator: category closure can be investigated for a master predicate,
-- excluded object, imagined global section and externalised residual.  The
-- interpretation remains candidate-only and does not prove political economy.
------------------------------------------------------------------------

record DrugCategoryIdeologicalClosureCandidate : Set₁ where
  constructor drugCategoryIdeologicalClosureCandidate
  field
    closure : Zizek.PNFIdeologicalClosure
    masterDrugPredicateReference : String
    excludedCarrierReference : String
    externalisedResidualReference : String
    categoryClosureCandidateOnly : Bool
    categoryClosureCandidateOnlyIsTrue :
      categoryClosureCandidateOnly ≡ true
    actualInstitutionalGluingStillRequired : Bool
    actualInstitutionalGluingStillRequiredIsTrue :
      actualInstitutionalGluingStillRequired ≡ true

open DrugCategoryIdeologicalClosureCandidate public

zizekBoundary : Zizek.PNFZizekAuthorityBoundary
zizekBoundary = Zizek.canonicalPNFZizekAuthorityBoundary

lacanZizekBoundary : LacanZizek.LacanZizekIdeologyBoundary
lacanZizekBoundary = LacanZizek.canonicalLacanZizekIdeologyBoundary

------------------------------------------------------------------------
-- Existing broad philosophy atlas is retained as audit lanes.
------------------------------------------------------------------------

philosophyBoundary : Philosophy.IntersectionalPowerValueFolkModelBoundary
philosophyBoundary = Philosophy.canonicalIntersectionalPowerValueFolkModelBoundary

criticalTheoryBoundary : Critical.HistoricalTotalityCriticalTheoryBoundary
criticalTheoryBoundary = Critical.canonicalHistoricalTotalityCriticalTheoryBoundary

------------------------------------------------------------------------
-- BIDI: a philosophical audit can generate a contest demand, but philosophy
-- alone does not manufacture the historical/empirical evidence or replacement
-- category.
------------------------------------------------------------------------

data AuditToContestReason : DrugCategoryAudit → Atlas.ContestReason → Set where
  wittgensteinUseToPracticeMismatch :
    AuditToContestReason wittgensteinUseAudit Atlas.usePracticeMismatch
  zizekClosureToHistoricalResidual :
    AuditToContestReason zizekClosureFantasyAudit Atlas.historicalResidueErased
  foucaultPowerToLegitimacyGap :
    AuditToContestReason foucaultPowerClassificationAudit Atlas.democraticLegitimacyGap
  marxMaterialToCommercialCapture :
    AuditToContestReason marxMaterialInterestAudit Atlas.commercialCaptureCandidate
  feministSubjectToSubjectErasure :
    AuditToContestReason feministSubjectPositionAudit Atlas.originatingSubjectPositionErased
  intersectionalToCommunityVoice :
    AuditToContestReason intersectionalAxisAudit Atlas.affectedCommunityVoiceErased
  levinasToSubjectErasure :
    AuditToContestReason levinasOtherExceedsChartAudit Atlas.originatingSubjectPositionErased
  derridaToHistoricalResidual :
    AuditToContestReason derridaNoFinalClosureAudit Atlas.historicalResidueErased

record PhilosophicallySeededContest
    (assertion : Atlas.CategoryAssertion)
    (audit : DrugCategoryAudit) : Set where
  constructor philosophicallySeededContest
  field
    auditReceipt : CategoryAuditReceipt assertion audit
    contestReason : Atlas.ContestReason
    auditSupportsReason : AuditToContestReason audit contestReason
    residualDemand : Atlas.ResidualCoordinate
    historicalEmpiricalEvidenceStillRequired : Bool
    historicalEmpiricalEvidenceStillRequiredIsTrue :
      historicalEmpiricalEvidenceStillRequired ≡ true

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data PhilosophyAuditPromotesEmpiricalCause : Set where

data WittgensteinUsePromotesPoliticalEconomy : Set where

data ZizekClosurePromotesInstitutionalFact : Set where

data FoucaultAuditPromotesOppressionFact : Set where

data MarxAuditPromotesCapitalistCause : Set where

data DerridaAuditPromotesNoTruth : Set where

philosophyAuditDoesNotPromoteEmpiricalCause :
  PhilosophyAuditPromotesEmpiricalCause → ⊥
philosophyAuditDoesNotPromoteEmpiricalCause ()

wittgensteinUseDoesNotPromotePoliticalEconomy :
  WittgensteinUsePromotesPoliticalEconomy → ⊥
wittgensteinUseDoesNotPromotePoliticalEconomy ()

zizekClosureDoesNotPromoteInstitutionalFact :
  ZizekClosurePromotesInstitutionalFact → ⊥
zizekClosureDoesNotPromoteInstitutionalFact ()

foucaultAuditDoesNotPromoteOppressionFact :
  FoucaultAuditPromotesOppressionFact → ⊥
foucaultAuditDoesNotPromoteOppressionFact ()

marxAuditDoesNotPromoteCapitalistCause :
  MarxAuditPromotesCapitalistCause → ⊥
marxAuditDoesNotPromoteCapitalistCause ()

derridaAuditDoesNotPromoteNoTruth : DerridaAuditPromotesNoTruth → ⊥
derridaAuditDoesNotPromoteNoTruth ()

record DrugCategoryPhilosophyOperatorBoundary : Set where
  constructor drugCategoryPhilosophyOperatorBoundary
  field
    philosophySuppliesAuditOperatorsNotMasterOntology : Bool
    philosophySuppliesAuditOperatorsNotMasterOntologyIsTrue :
      philosophySuppliesAuditOperatorsNotMasterOntology ≡ true
    wittgensteinUseCanReopenLexicallyStableCategory : Bool
    wittgensteinUseCanReopenLexicallyStableCategoryIsTrue :
      wittgensteinUseCanReopenLexicallyStableCategory ≡ true
    zizekClosureCanExposeExcludedResidualCandidate : Bool
    zizekClosureCanExposeExcludedResidualCandidateIsTrue :
      zizekClosureCanExposeExcludedResidualCandidate ≡ true
    philosophicalAuditAutomaticallyProvesEmpiricalCause : Bool
    philosophicalAuditAutomaticallyProvesEmpiricalCauseIsFalse :
      philosophicalAuditAutomaticallyProvesEmpiricalCause ≡ false
    sameKeywordAcrossPhilosophersMeansSameConcept : Bool
    sameKeywordAcrossPhilosophersMeansSameConceptIsFalse :
      sameKeywordAcrossPhilosophersMeansSameConcept ≡ false
    philosophicalContestAutomaticallySelectsReplacementCategory : Bool
    philosophicalContestAutomaticallySelectsReplacementCategoryIsFalse :
      philosophicalContestAutomaticallySelectsReplacementCategory ≡ false

canonicalDrugCategoryPhilosophyOperatorBoundary :
  DrugCategoryPhilosophyOperatorBoundary
canonicalDrugCategoryPhilosophyOperatorBoundary =
  drugCategoryPhilosophyOperatorBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
