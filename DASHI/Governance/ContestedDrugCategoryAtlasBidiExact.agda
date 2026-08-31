module DASHI.Governance.ContestedDrugCategoryAtlasBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Rechart
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Authority
import DASHI.Governance.DrugClassificationLegitimacyAssayExact as Legitimacy
import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical

------------------------------------------------------------------------
-- CONTESTED DRUG-CATEGORY ATLAS, BIDI
--
-- Forward direction: an issuer/practice/history produces a category claim.
-- Backward direction: affected subjects/communities can contest that claim and
-- request a rechart by supplying a residual coordinate erased by the inherited
-- chart.  No one atlas is promoted to a global ontology.
------------------------------------------------------------------------

data CategoryChart : Set where
  stateLegalChart
  enforcementChart
  biomedicalChart
  veteranClinicalChart
  commercialChart
  livedSubjectChart
  affectedCommunityChart
  indigenousSovereignChart
  : CategoryChart

data CategoryUsePractice : Set where
  prohibitUse
  policeUse
  diagnoseUse
  treatUse
  researchUse
  commercialiseUse
  selfDescribeUse
  communityGovernUse
  ceremonialGovernUse
  : CategoryUsePractice

data ContestedSubject : Set where
  genericDrugCarrier
  countercultureCarrier
  veteranCarrier
  regulatedPatientCarrier
  criminalizedCarrier
  commercialConsumerCarrier
  indigenousCeremonialCarrier
  : ContestedSubject

record CategoryAssertion : Set where
  constructor categoryAssertion
  field
    subject : ContestedSubject
    chart : CategoryChart
    issuer : Authority.CategoryIssuer
    category : Authority.DrugCategory
    practice : CategoryUsePractice
    historicalVersion : Historical.ClassifierVersion
    authorityKind : Authority.ClassificationAuthorityKind
    sourceReference : String

open CategoryAssertion public

------------------------------------------------------------------------
-- BIDI contest surface.
------------------------------------------------------------------------

data ContestReason : Set where
  originatingSubjectPositionErased
  affectedCommunityVoiceErased
  usePracticeMismatch
  historicalResidueErased
  clinicalEvidenceMismatch
  democraticLegitimacyGap
  indigenousSovereigntyErased
  commercialCaptureCandidate
  : ContestReason

data ResidualCoordinate : Set where
  subjectAuthorshipResidual
  communityVoiceResidual
  usePracticeResidual
  historicalPathResidual
  clinicalNeedResidual
  legitimacyResidual
  sovereigntyResidual
  materialBenefitResidual
  : ResidualCoordinate

record CategoryContest (assertion : CategoryAssertion) : Set where
  constructor categoryContest
  field
    reason : ContestReason
    residual : ResidualCoordinate
    contestingIssuer : Authority.CategoryIssuer
    evidenceReference : String
    authorityReference : String
    requestedRechartReference : String

open CategoryContest public

record RechartReceipt (assertion : CategoryAssertion) : Set where
  constructor rechartReceipt
  field
    contest : CategoryContest assertion
    replacementChart : CategoryChart
    replacementCategory : Authority.DrugCategory
    replacementPractice : CategoryUsePractice
    newResidualRetained : Bool
    newResidualRetainedIsTrue : newResidualRetained ≡ true
    oldChartHistoryRetained : Bool
    oldChartHistoryRetainedIsTrue : oldChartHistoryRetained ≡ true
    rechartAuthorityReference : String
    rechartDoesNotClaimGlobalOntology : Bool
    rechartDoesNotClaimGlobalOntologyIsTrue :
      rechartDoesNotClaimGlobalOntology ≡ true

------------------------------------------------------------------------
-- Same lexical category can arise from different charts and practices.
------------------------------------------------------------------------

data PatientUseState : Set where
  stateAdminPatient
  clinicalCarePatient
  selfSituatedPatient
  : PatientUseState

data PatientWord : Set where samePatientWord : PatientWord

data PatientPracticeCode : Set where
  administrativePatientCode
  clinicalPatientCode
  livedPatientCode
  : PatientPracticeCode

patientWord : PatientUseState → PatientWord
patientWord _ = samePatientWord

patientPractice : PatientUseState → PatientPracticeCode
patientPractice stateAdminPatient = administrativePatientCode
patientPractice clinicalCarePatient = clinicalPatientCode
patientPractice selfSituatedPatient = livedPatientCode

samePatientWordCannotRecoverPractice :
  INF.FactorsThrough patientWord patientPractice → ⊥
samePatientWordCannotRecoverPractice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      stateAdminPatient clinicalCarePatient refl (λ ()))

------------------------------------------------------------------------
-- Positive BIDI repair must add information, not merely rename an old chart.
------------------------------------------------------------------------

data FlatDrugChart : Set where sameFlatDrugCode : FlatDrugChart

data FineDrugState : Set where
  externallyNamedState selfAuthoredState : FineDrugState

data AuthorshipResidual : Set where
  externalAuthorship selfAuthorship : AuthorshipResidual

flatDrugChart : FineDrugState → FlatDrugChart
flatDrugChart _ = sameFlatDrugCode

authorshipResidual : FineDrugState → AuthorshipResidual
authorshipResidual externallyNamedState = externalAuthorship
authorshipResidual selfAuthoredState = selfAuthorship

canonicalDrugPositiveRecharting : Rechart.PositiveRecharting flatDrugChart
canonicalDrugPositiveRecharting =
  Rechart.positive-recharting
    authorshipResidual
    externallyNamedState
    selfAuthoredState
    refl
    (λ ())

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ContestPromotesCorrectReplacement : Set where

data SelfDescriptionPromotesGlobalCategoryAuthority : Set where

data StateCategoryPromotesGlobalSemanticAuthority : Set where

data RechartPromotesHistoricalErasure : Set where

data PositiveRechartPromotesEmpiricalPopulationClaim : Set where

contestDoesNotPromoteCorrectReplacement : ContestPromotesCorrectReplacement → ⊥
contestDoesNotPromoteCorrectReplacement ()

selfDescriptionDoesNotPromoteGlobalAuthority :
  SelfDescriptionPromotesGlobalCategoryAuthority → ⊥
selfDescriptionDoesNotPromoteGlobalAuthority ()

stateCategoryDoesNotPromoteGlobalSemanticAuthority :
  StateCategoryPromotesGlobalSemanticAuthority → ⊥
stateCategoryDoesNotPromoteGlobalSemanticAuthority ()

rechartDoesNotPromoteHistoricalErasure : RechartPromotesHistoricalErasure → ⊥
rechartDoesNotPromoteHistoricalErasure ()

positiveRechartDoesNotPromotePopulationClaim :
  PositiveRechartPromotesEmpiricalPopulationClaim → ⊥
positiveRechartDoesNotPromotePopulationClaim ()

legitimacyBoundary : Legitimacy.DrugClassificationLegitimacyBoundary
legitimacyBoundary = Legitimacy.canonicalDrugClassificationLegitimacyBoundary

authorityBoundary : Authority.FeministDrugClassificationAuthorityBoundary
authorityBoundary = Authority.canonicalFeministDrugClassificationAuthorityBoundary

record ContestedDrugCategoryAtlasBoundary : Set where
  constructor contestedDrugCategoryAtlasBoundary
  field
    forwardClassificationAndBackwardContestAreDistinct : Bool
    forwardClassificationAndBackwardContestAreDistinctIsTrue :
      forwardClassificationAndBackwardContestAreDistinct ≡ true
    sameWordCanHaveDifferentUsePractice : Bool
    sameWordCanHaveDifferentUsePracticeIsTrue :
      sameWordCanHaveDifferentUsePractice ≡ true
    validContestAutomaticallyDeterminesReplacement : Bool
    validContestAutomaticallyDeterminesReplacementIsFalse :
      validContestAutomaticallyDeterminesReplacement ≡ false
    positiveRepairMustAddResidualInformation : Bool
    positiveRepairMustAddResidualInformationIsTrue :
      positiveRepairMustAddResidualInformation ≡ true
    oneChartHasGlobalSubjectDefinitionAuthority : Bool
    oneChartHasGlobalSubjectDefinitionAuthorityIsFalse :
      oneChartHasGlobalSubjectDefinitionAuthority ≡ false
    rechartingErasesHistoricalClassifierPath : Bool
    rechartingErasesHistoricalClassifierPathIsFalse :
      rechartingErasesHistoricalClassifierPath ≡ false

canonicalContestedDrugCategoryAtlasBoundary : ContestedDrugCategoryAtlasBoundary
canonicalContestedDrugCategoryAtlasBoundary =
  contestedDrugCategoryAtlasBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
