module DASHI.Governance.DrugCategoryConsumerIndexedTranslationAdmissionExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact as Path

------------------------------------------------------------------------
-- CONSUMER-INDEXED TRANSLATION ADMISSION
--
-- A chart path is not globally safe/unsafe.  Admission is relative to the
-- coordinates required by a declared downstream consumer.
------------------------------------------------------------------------

data TranslationConsumer : Set where
  clinicalSafetyConsumer
  livedSubjectAuthorityConsumer
  historicalContinuityConsumer
  sovereignAuthorityConsumer
  commercialBenefitConsumer
  : TranslationConsumer

data RequiresCoordinate :
    TranslationConsumer → Translation.TranslationCoordinate → Set where
  clinicalRequiresClinicalFact :
    RequiresCoordinate
      clinicalSafetyConsumer Translation.clinicalFactCoordinate

  livedSubjectRequiresAuthorship :
    RequiresCoordinate
      livedSubjectAuthorityConsumer Translation.subjectAuthorshipCoordinate
  livedSubjectRequiresHistory :
    RequiresCoordinate
      livedSubjectAuthorityConsumer Translation.historicalPathCoordinate

  historicalConsumerRequiresHistory :
    RequiresCoordinate
      historicalContinuityConsumer Translation.historicalPathCoordinate

  sovereignConsumerRequiresAuthority :
    RequiresCoordinate
      sovereignAuthorityConsumer Translation.sovereignAuthorityCoordinate

  commercialConsumerRequiresBenefit :
    RequiresCoordinate
      commercialBenefitConsumer Translation.materialBenefitCoordinate

ConsumerPathSafe :
  ∀ {source target} →
  TranslationConsumer →
  Path.TranslationPath source target → Set
ConsumerPathSafe consumer path =
  ∀ {coordinate} →
  RequiresCoordinate consumer coordinate →
  Path.CoordinatePreserved path coordinate

clinicalSafetyAdmitsStateClinicalLived :
  ConsumerPathSafe clinicalSafetyConsumer Path.stateClinicalLivedPath
clinicalSafetyAdmitsStateClinicalLived clinicalRequiresClinicalFact =
  Path.clinicalFactPreservedAlongStateClinicalLived

livedSubjectAuthorityRejectsStateClinicalLived :
  ConsumerPathSafe livedSubjectAuthorityConsumer Path.stateClinicalLivedPath → ⊥
livedSubjectAuthorityRejectsStateClinicalLived safe =
  Path.subjectAuthorshipNotPreservedAlongStateClinicalLived
    (safe livedSubjectRequiresAuthorship)

historicalContinuityRejectsStateClinicalLived :
  ConsumerPathSafe historicalContinuityConsumer Path.stateClinicalLivedPath → ⊥
historicalContinuityRejectsStateClinicalLived safe =
  Path.historicalPathNotPreservedAlongStateClinicalLived
    (safe historicalConsumerRequiresHistory)

sovereignAuthorityRejectsIndigenousCommercial :
  ConsumerPathSafe sovereignAuthorityConsumer Path.indigenousCommercialPath → ⊥
sovereignAuthorityRejectsIndigenousCommercial safe with
  safe sovereignConsumerRequiresAuthority
... | Path.preservedStep () rest

------------------------------------------------------------------------
-- The same path can therefore be admitted for one consumer and rejected for
-- another without any inconsistency.
------------------------------------------------------------------------

record ConsumerRelativeAdmissionSeparation : Set where
  constructor consumerRelativeAdmissionSeparation
  field
    clinicalSafe :
      ConsumerPathSafe clinicalSafetyConsumer Path.stateClinicalLivedPath
    livedSubjectUnsafe :
      ConsumerPathSafe livedSubjectAuthorityConsumer Path.stateClinicalLivedPath → ⊥
    historyUnsafe :
      ConsumerPathSafe historicalContinuityConsumer Path.stateClinicalLivedPath → ⊥

canonicalConsumerRelativeAdmissionSeparation :
  ConsumerRelativeAdmissionSeparation
canonicalConsumerRelativeAdmissionSeparation =
  consumerRelativeAdmissionSeparation
    clinicalSafetyAdmitsStateClinicalLived
    livedSubjectAuthorityRejectsStateClinicalLived
    historicalContinuityRejectsStateClinicalLived

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SafeForOneConsumerPromotesGlobalSafety : Set where

data ClinicalSafetyPromotesHistoricalContinuity : Set where

data MedicalLegibilityPromotesSubjectAuthority : Set where

data CommercialAccessPromotesSovereignAuthority : Set where

oneConsumerSafetyDoesNotPromoteGlobalSafety :
  SafeForOneConsumerPromotesGlobalSafety → ⊥
oneConsumerSafetyDoesNotPromoteGlobalSafety ()

clinicalSafetyDoesNotPromoteHistoricalContinuity :
  ClinicalSafetyPromotesHistoricalContinuity → ⊥
clinicalSafetyDoesNotPromoteHistoricalContinuity ()

medicalLegibilityDoesNotPromoteSubjectAuthority :
  MedicalLegibilityPromotesSubjectAuthority → ⊥
medicalLegibilityDoesNotPromoteSubjectAuthority ()

commercialAccessDoesNotPromoteSovereignAuthority :
  CommercialAccessPromotesSovereignAuthority → ⊥
commercialAccessDoesNotPromoteSovereignAuthority ()

record DrugCategoryConsumerIndexedTranslationBoundary : Set where
  constructor drugCategoryConsumerIndexedTranslationBoundary
  field
    translationSafetyIsConsumerIndexed : Bool
    translationSafetyIsConsumerIndexedIsTrue :
      translationSafetyIsConsumerIndexed ≡ true
    onePathCanBeSafeForClinicalButUnsafeForSubjectHistory : Bool
    onePathCanBeSafeForClinicalButUnsafeForSubjectHistoryIsTrue :
      onePathCanBeSafeForClinicalButUnsafeForSubjectHistory ≡ true
    sovereignCommercialPathIsAuthoritySafe : Bool
    sovereignCommercialPathIsAuthoritySafeIsFalse :
      sovereignCommercialPathIsAuthoritySafe ≡ false
    oneConsumerSafetyImpliesGlobalTranslationSafety : Bool
    oneConsumerSafetyImpliesGlobalTranslationSafetyIsFalse :
      oneConsumerSafetyImpliesGlobalTranslationSafety ≡ false

canonicalDrugCategoryConsumerIndexedTranslationBoundary :
  DrugCategoryConsumerIndexedTranslationBoundary
canonicalDrugCategoryConsumerIndexedTranslationBoundary =
  drugCategoryConsumerIndexedTranslationBoundary
    true refl
    true refl
    false refl
    false refl
