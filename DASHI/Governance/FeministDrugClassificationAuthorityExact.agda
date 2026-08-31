module DASHI.Governance.FeministDrugClassificationAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Governance.FeministRecognitionAuthorityCrossPollinationExact as Feminist
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical

------------------------------------------------------------------------
-- FEMINIST x DRUG-CLASSIFICATION AUTHORITY
--
-- Reuses the feminist recognition/category/subject-position theorem pattern:
-- having power to impose a category does not create epistemic, clinical,
-- democratic, originating-subject or sovereign authority.  Classification is
-- therefore represented as an authority fibre, not a single scalar power.
------------------------------------------------------------------------

data DrugCategory : Set where
  illicitDrugCategory
  medicineCategory
  patientCategory
  addictCategory
  criminalCategory
  veteranTherapeuticCategory
  psychedelicCategory
  ceremonialMedicineCategory
  commercialWellnessCategory
  : DrugCategory

data CategoryIssuer : Set where
  federalExecutiveIssuer
  enforcementAgencyIssuer
  regulatorIssuer
  medicalProfessionIssuer
  veteranHealthSystemIssuer
  commercialSponsorIssuer
  affectedPersonIssuer
  drugUserCommunityIssuer
  indigenousSovereignCommunityIssuer
  : CategoryIssuer

data ClassificationAuthorityKind : Set where
  coerciveImpositionAuthority
  legalAdministrativeAuthority
  empiricalEpistemicAuthority
  clinicalAuthority
  originatingSubjectAuthority
  affectedCommunityAuthority
  democraticMandateAuthority
  commercialMarketAuthority
  indigenousSovereignAuthority
  : ClassificationAuthorityKind

record ClassificationAuthorityReceipt : Set where
  constructor classificationAuthorityReceipt
  field
    issuer : CategoryIssuer
    category : DrugCategory
    authorityKind : ClassificationAuthorityKind
    sourceReference : String
    scopeReference : String
    contestabilityReference : String

open ClassificationAuthorityReceipt public

------------------------------------------------------------------------
-- Same visible category can hide different originating authority positions.
------------------------------------------------------------------------

data CategoryState : Set where
  externallyClassifiedPatient
  selfSituatedPatient
  : CategoryState

data VisibleCategory : Set where
  samePatientCategory : VisibleCategory

data OriginatingPosition : Set where
  representedPatientPosition
  originatingPatientPosition
  : OriginatingPosition

visibleCategory : CategoryState → VisibleCategory
visibleCategory externallyClassifiedPatient = samePatientCategory
visibleCategory selfSituatedPatient = samePatientCategory

originatingPosition : CategoryState → OriginatingPosition
originatingPosition externallyClassifiedPatient = representedPatientPosition
originatingPosition selfSituatedPatient = originatingPatientPosition

originatingPositionDiffers :
  originatingPosition externallyClassifiedPatient
  ≡ originatingPosition selfSituatedPatient → ⊥
originatingPositionDiffers ()

patientCategoryCannotRecoverOriginatingPosition :
  INF.FactorsThrough visibleCategory originatingPosition → ⊥
patientCategoryCannotRecoverOriginatingPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      externallyClassifiedPatient selfSituatedPatient
      refl originatingPositionDiffers)

------------------------------------------------------------------------
-- Imposition power does not collapse the authority fibre.
------------------------------------------------------------------------

data ImpositionPromotesEpistemicAuthority : Set where

data ImpositionPromotesClinicalAuthority : Set where

data ImpositionPromotesOriginatingSubjectAuthority : Set where

data ImpositionPromotesDemocraticMandate : Set where

data ImpositionPromotesIndigenousSovereignty : Set where

data EmpiricalAdequacyPromotesCategoryAuthority : Set where

impositionDoesNotPromoteEpistemic : ImpositionPromotesEpistemicAuthority → ⊥
impositionDoesNotPromoteEpistemic ()

impositionDoesNotPromoteClinical : ImpositionPromotesClinicalAuthority → ⊥
impositionDoesNotPromoteClinical ()

impositionDoesNotPromoteOriginatingSubject :
  ImpositionPromotesOriginatingSubjectAuthority → ⊥
impositionDoesNotPromoteOriginatingSubject ()

impositionDoesNotPromoteDemocraticMandate :
  ImpositionPromotesDemocraticMandate → ⊥
impositionDoesNotPromoteDemocraticMandate ()

impositionDoesNotPromoteIndigenousSovereignty :
  ImpositionPromotesIndigenousSovereignty → ⊥
impositionDoesNotPromoteIndigenousSovereignty ()

empiricalAdequacyDoesNotPromoteCategoryAuthority :
  EmpiricalAdequacyPromotesCategoryAuthority → ⊥
empiricalAdequacyDoesNotPromoteCategoryAuthority ()

------------------------------------------------------------------------
-- Feminist/source-neutral bridges.
------------------------------------------------------------------------

feministBoundary : Feminist.FeministRecognitionCrossPollinationBoundary
feministBoundary = Feminist.canonicalFeministRecognitionCrossPollinationBoundary

subjectBoundary : Subject.RepresentationSubjectPositionBoundary
subjectBoundary = Subject.canonicalRepresentationSubjectPositionBoundary

situatedBoundary : Situated.SituatedClaimAuthorityBoundary
situatedBoundary = Situated.canonicalSituatedClaimAuthorityBoundary

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

historicalBoundary : Historical.HistoricalDrugGovernanceClassifierBoundary
historicalBoundary = Historical.canonicalHistoricalDrugGovernanceClassifierBoundary

------------------------------------------------------------------------
-- Classification grammar is relational.  Keeping the same drug/carrier domain
-- does not force one one-centred state grammar over medical, lived, ceremonial
-- or community-authored grammars.
------------------------------------------------------------------------

data SharedDrugCarrier : Set where
  sharedPsychoactiveCarrier : SharedDrugCarrier

data ClassificationGrammar : Set where
  stateCentredGrammar
  clinicalRelationalGrammar
  livedSubjectGrammar
  sovereignCeremonialGrammar
  : ClassificationGrammar

record SituatedDrugClassification : Set where
  constructor situatedDrugClassification
  field
    carrier : SharedDrugCarrier
    grammar : ClassificationGrammar
    issuer : CategoryIssuer
    category : DrugCategory

open SituatedDrugClassification public

statePatientClassification : SituatedDrugClassification
statePatientClassification = situatedDrugClassification
  sharedPsychoactiveCarrier
  stateCentredGrammar
  federalExecutiveIssuer
  patientCategory

selfSituatedPatientClassification : SituatedDrugClassification
selfSituatedPatientClassification = situatedDrugClassification
  sharedPsychoactiveCarrier
  livedSubjectGrammar
  affectedPersonIssuer
  patientCategory

sameCarrierAndCategoryDifferentGrammar :
  grammar statePatientClassification
  ≡ grammar selfSituatedPatientClassification → ⊥
sameCarrierAndCategoryDifferentGrammar ()

record FeministDrugClassificationAuthorityBoundary : Set where
  constructor feministDrugClassificationAuthorityBoundary
  field
    abilityToImposeCategoryEqualsEpistemicAuthority : Bool
    abilityToImposeCategoryEqualsEpistemicAuthorityIsFalse :
      abilityToImposeCategoryEqualsEpistemicAuthority ≡ false
    legalAdministrativeAuthorityEqualsClinicalAuthority : Bool
    legalAdministrativeAuthorityEqualsClinicalAuthorityIsFalse :
      legalAdministrativeAuthorityEqualsClinicalAuthority ≡ false
    visibleCategoryRecoversOriginatingSubjectPosition : Bool
    visibleCategoryRecoversOriginatingSubjectPositionIsFalse :
      visibleCategoryRecoversOriginatingSubjectPosition ≡ false
    sameCarrierAndCategoryImpliesSameRelationalGrammar : Bool
    sameCarrierAndCategoryImpliesSameRelationalGrammarIsFalse :
      sameCarrierAndCategoryImpliesSameRelationalGrammar ≡ false
    biomedicalRecognitionTransfersIndigenousSovereignty : Bool
    biomedicalRecognitionTransfersIndigenousSovereigntyIsFalse :
      biomedicalRecognitionTransfersIndigenousSovereignty ≡ false
    classifierRevisionAutomaticallyImprovesLegitimacy : Bool
    classifierRevisionAutomaticallyImprovesLegitimacyIsFalse :
      classifierRevisionAutomaticallyImprovesLegitimacy ≡ false

canonicalFeministDrugClassificationAuthorityBoundary :
  FeministDrugClassificationAuthorityBoundary
canonicalFeministDrugClassificationAuthorityBoundary =
  feministDrugClassificationAuthorityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
