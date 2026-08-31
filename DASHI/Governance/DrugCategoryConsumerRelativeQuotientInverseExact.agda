module DASHI.Governance.DrugCategoryConsumerRelativeQuotientInverseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact as Path
import DASHI.Governance.DrugCategoryConsumerIndexedTranslationAdmissionExact as Admission

------------------------------------------------------------------------
-- CONSUMER-RELATIVE QUOTIENT INVERSE
--
-- "Inverse" is intentionally quotient-relative.  We do NOT construct a full
-- semantic inverse between state/legal, biomedical, lived, commercial or
-- sovereign charts.  Instead, a path admits a consumer-relative inverse exactly
-- when every coordinate required by that consumer survives the path.
--
-- Thus a state -> clinical -> lived path can be reversible for the narrow
-- clinical-fact quotient while remaining non-invertible for originating subject
-- authority or historical continuity.
------------------------------------------------------------------------

record ConsumerRelativeQuotientInverse
    {source target}
    (consumer : Admission.TranslationConsumer)
    (path : Path.TranslationPath source target) : Set where
  constructor consumerRelativeQuotientInverse
  field
    requiredCoordinateReadback :
      ∀ {coordinate} →
      Admission.RequiresCoordinate consumer coordinate →
      Path.CoordinatePreserved path coordinate
    forwardReference : String
    backwardReadbackReference : String
    fullChartInverseClaimed : Bool
    fullChartInverseClaimedIsFalse : fullChartInverseClaimed ≡ false

open ConsumerRelativeQuotientInverse public

consumerSafePathCreatesQuotientInverse :
  ∀ {source target consumer}
    {path : Path.TranslationPath source target} →
  Admission.ConsumerPathSafe consumer path →
  ConsumerRelativeQuotientInverse consumer path
consumerSafePathCreatesQuotientInverse safe =
  consumerRelativeQuotientInverse
    safe
    "forward translation path preserves every coordinate required by the declared consumer"
    "backward readback is only on the consumer quotient; no whole-chart semantic inverse is asserted"
    false refl

quotientInverseCreatesConsumerSafety :
  ∀ {source target consumer}
    {path : Path.TranslationPath source target} →
  ConsumerRelativeQuotientInverse consumer path →
  Admission.ConsumerPathSafe consumer path
quotientInverseCreatesConsumerSafety inverse =
  requiredCoordinateReadback inverse

------------------------------------------------------------------------
-- Canonical clinical quotient inverse.
------------------------------------------------------------------------

clinicalQuotientInverseOnStateClinicalLived :
  ConsumerRelativeQuotientInverse
    Admission.clinicalSafetyConsumer
    Path.stateClinicalLivedPath
clinicalQuotientInverseOnStateClinicalLived =
  consumerSafePathCreatesQuotientInverse
    Admission.clinicalSafetyAdmitsStateClinicalLived

------------------------------------------------------------------------
-- Exact non-invertibility on erased consumer coordinates.
------------------------------------------------------------------------

livedSubjectQuotientNotInvertibleOnStateClinicalLived :
  ConsumerRelativeQuotientInverse
    Admission.livedSubjectAuthorityConsumer
    Path.stateClinicalLivedPath → ⊥
livedSubjectQuotientNotInvertibleOnStateClinicalLived inverse =
  Admission.livedSubjectAuthorityRejectsStateClinicalLived
    (quotientInverseCreatesConsumerSafety inverse)

historicalQuotientNotInvertibleOnStateClinicalLived :
  ConsumerRelativeQuotientInverse
    Admission.historicalContinuityConsumer
    Path.stateClinicalLivedPath → ⊥
historicalQuotientNotInvertibleOnStateClinicalLived inverse =
  Admission.historicalContinuityRejectsStateClinicalLived
    (quotientInverseCreatesConsumerSafety inverse)

sovereignQuotientNotInvertibleOnIndigenousCommercial :
  ConsumerRelativeQuotientInverse
    Admission.sovereignAuthorityConsumer
    Path.indigenousCommercialPath → ⊥
sovereignQuotientNotInvertibleOnIndigenousCommercial inverse =
  Admission.sovereignAuthorityRejectsIndigenousCommercial
    (quotientInverseCreatesConsumerSafety inverse)

------------------------------------------------------------------------
-- Same translation path can therefore be invertible on one quotient and
-- non-invertible on another.
------------------------------------------------------------------------

record ConsumerRelativeInverseSeparation : Set where
  constructor consumerRelativeInverseSeparation
  field
    clinicalInverseExists :
      ConsumerRelativeQuotientInverse
        Admission.clinicalSafetyConsumer
        Path.stateClinicalLivedPath
    subjectInverseImpossible :
      ConsumerRelativeQuotientInverse
        Admission.livedSubjectAuthorityConsumer
        Path.stateClinicalLivedPath → ⊥
    historyInverseImpossible :
      ConsumerRelativeQuotientInverse
        Admission.historicalContinuityConsumer
        Path.stateClinicalLivedPath → ⊥

canonicalConsumerRelativeInverseSeparation :
  ConsumerRelativeInverseSeparation
canonicalConsumerRelativeInverseSeparation =
  consumerRelativeInverseSeparation
    clinicalQuotientInverseOnStateClinicalLived
    livedSubjectQuotientNotInvertibleOnStateClinicalLived
    historicalQuotientNotInvertibleOnStateClinicalLived

------------------------------------------------------------------------
-- BIDI readback remains consumer-limited.
------------------------------------------------------------------------

data QuotientInversePromotesFullChartInverse : Set where

data ClinicalInversePromotesHistoricalRecovery : Set where

data ClinicalInversePromotesSubjectAuthorityRecovery : Set where

data CommercialLegibilityPromotesSovereignInverse : Set where

quotientInverseDoesNotPromoteFullChartInverse :
  QuotientInversePromotesFullChartInverse → ⊥
quotientInverseDoesNotPromoteFullChartInverse ()

clinicalInverseDoesNotPromoteHistoricalRecovery :
  ClinicalInversePromotesHistoricalRecovery → ⊥
clinicalInverseDoesNotPromoteHistoricalRecovery ()

clinicalInverseDoesNotPromoteSubjectAuthorityRecovery :
  ClinicalInversePromotesSubjectAuthorityRecovery → ⊥
clinicalInverseDoesNotPromoteSubjectAuthorityRecovery ()

commercialLegibilityDoesNotPromoteSovereignInverse :
  CommercialLegibilityPromotesSovereignInverse → ⊥
commercialLegibilityDoesNotPromoteSovereignInverse ()

record DrugCategoryConsumerRelativeQuotientInverseBoundary : Set where
  constructor drugCategoryConsumerRelativeQuotientInverseBoundary
  field
    inverseIsConsumerQuotientRelative : Bool
    inverseIsConsumerQuotientRelativeIsTrue :
      inverseIsConsumerQuotientRelative ≡ true
    onePathCanBeInvertibleForClinicalButNotHistory : Bool
    onePathCanBeInvertibleForClinicalButNotHistoryIsTrue :
      onePathCanBeInvertibleForClinicalButNotHistory ≡ true
    quotientInverseMeansFullSemanticInverse : Bool
    quotientInverseMeansFullSemanticInverseIsFalse :
      quotientInverseMeansFullSemanticInverse ≡ false
    commercialTranslationHasAutomaticSovereignInverse : Bool
    commercialTranslationHasAutomaticSovereignInverseIsFalse :
      commercialTranslationHasAutomaticSovereignInverse ≡ false

canonicalDrugCategoryConsumerRelativeQuotientInverseBoundary :
  DrugCategoryConsumerRelativeQuotientInverseBoundary
canonicalDrugCategoryConsumerRelativeQuotientInverseBoundary =
  drugCategoryConsumerRelativeQuotientInverseBoundary
    true refl
    true refl
    false refl
    false refl
