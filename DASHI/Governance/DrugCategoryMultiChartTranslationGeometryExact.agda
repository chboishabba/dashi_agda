module DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ContextGovernedLineageTransportExact as Lineage
import DASHI.Core.GovernedObservationProvenanceExact as Provenance
import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Authority
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous

------------------------------------------------------------------------
-- MULTI-CHART TRANSLATION GEOMETRY
--
-- A translation between category charts is not assumed to be semantics-,
-- history-, authority- or provenance-preserving.  Translation is BIDI:
--   forward: source chart -> target chart surface;
--   backward: target surface -> reconstruction/contest obligations.
-- Loss is coordinate-indexed and deposits explicit residuals.
------------------------------------------------------------------------

data TranslationCoordinate : Set where
  lexicalCategoryCoordinate
  usePracticeCoordinate
  clinicalFactCoordinate
  subjectAuthorshipCoordinate
  communityVoiceCoordinate
  historicalPathCoordinate
  democraticLegitimacyCoordinate
  materialBenefitCoordinate
  sovereignAuthorityCoordinate
  : TranslationCoordinate

data TranslationStatus : Set where
  preservedExactly
  translatedWithResidual
  erasedInTarget
  introducedInTarget
  unresolvedTranslation
  : TranslationStatus

record ChartTranslation : Set where
  constructor chartTranslation
  field
    sourceChart : Atlas.CategoryChart
    targetChart : Atlas.CategoryChart
    translateCategory : Authority.DrugCategory → Authority.DrugCategory
    coordinateStatus : TranslationCoordinate → TranslationStatus
    translationReference : String
    backwardReconstructionReference : String

open ChartTranslation public

------------------------------------------------------------------------
-- Canonical state -> clinical translation.
--
-- Local safety/clinical legibility can be retained while historical path and
-- originating-subject position are not automatically preserved.
------------------------------------------------------------------------

stateToClinical : ChartTranslation
stateToClinical = chartTranslation
  Atlas.stateLegalChart
  Atlas.biomedicalChart
  (λ
    { Authority.illicitDrugCategory → Authority.medicineCategory
    ; Authority.criminalCategory → Authority.patientCategory
    ; category → category
    })
  (λ
    { lexicalCategoryCoordinate → translatedWithResidual
    ; usePracticeCoordinate → translatedWithResidual
    ; clinicalFactCoordinate → preservedExactly
    ; subjectAuthorshipCoordinate → erasedInTarget
    ; communityVoiceCoordinate → unresolvedTranslation
    ; historicalPathCoordinate → erasedInTarget
    ; democraticLegitimacyCoordinate → unresolvedTranslation
    ; materialBenefitCoordinate → unresolvedTranslation
    ; sovereignAuthorityCoordinate → unresolvedTranslation
    })
  "state/legal -> biomedical translation may preserve clinical/safety facts while changing lexical/practice grammar"
  "reconstruct subject-position and historical-path residuals before treating biomedical chart as semantically complete"

------------------------------------------------------------------------
-- Canonical clinical -> lived translation.
------------------------------------------------------------------------

clinicalToLived : ChartTranslation
clinicalToLived = chartTranslation
  Atlas.biomedicalChart
  Atlas.livedSubjectChart
  (λ category → category)
  (λ
    { lexicalCategoryCoordinate → translatedWithResidual
    ; usePracticeCoordinate → translatedWithResidual
    ; clinicalFactCoordinate → preservedExactly
    ; subjectAuthorshipCoordinate → introducedInTarget
    ; communityVoiceCoordinate → unresolvedTranslation
    ; historicalPathCoordinate → translatedWithResidual
    ; democraticLegitimacyCoordinate → unresolvedTranslation
    ; materialBenefitCoordinate → unresolvedTranslation
    ; sovereignAuthorityCoordinate → unresolvedTranslation
    })
  "biomedical -> lived-subject translation retains clinical fact while introducing self-position coordinates"
  "introduced self-description is not retrospective restoration of an erased originating position"

------------------------------------------------------------------------
-- Sovereign/community translations can be blocked on authority preservation.
------------------------------------------------------------------------

data AuthorityPreservingTranslation : ChartTranslation → Set where
  authorityPreserving :
    ∀ {translation} →
    coordinateStatus translation sovereignAuthorityCoordinate ≡ preservedExactly →
    AuthorityPreservingTranslation translation

stateToClinicalNotAuthorityPreserving :
  AuthorityPreservingTranslation stateToClinical → ⊥
stateToClinicalNotAuthorityPreserving (authorityPreserving ())

indigenousToCommercial : ChartTranslation
indigenousToCommercial = chartTranslation
  Atlas.indigenousSovereignChart
  Atlas.commercialChart
  (λ
    { Authority.ceremonialMedicineCategory → Authority.commercialWellnessCategory
    ; category → category
    })
  (λ
    { lexicalCategoryCoordinate → translatedWithResidual
    ; usePracticeCoordinate → translatedWithResidual
    ; clinicalFactCoordinate → unresolvedTranslation
    ; subjectAuthorshipCoordinate → erasedInTarget
    ; communityVoiceCoordinate → erasedInTarget
    ; historicalPathCoordinate → erasedInTarget
    ; democraticLegitimacyCoordinate → unresolvedTranslation
    ; materialBenefitCoordinate → translatedWithResidual
    ; sovereignAuthorityCoordinate → erasedInTarget
    })
  "synthetic sovereign ceremonial -> commercial chart translation exposes possible extraction loss"
  "no authority-preserving inverse is supplied; community protocol/permission/sovereignty remain external obligations"

indigenousToCommercialNotAuthorityPreserving :
  AuthorityPreservingTranslation indigenousToCommercial → ⊥
indigenousToCommercialNotAuthorityPreserving (authorityPreserving ())

------------------------------------------------------------------------
-- Lineage specialization: erasure followed by downstream addition is new
-- information, not restoration of inherited authority/history.
------------------------------------------------------------------------

data TranslationContext : Set where
  stateContext clinicalContext livedContext : TranslationContext

translationLineage :
  Lineage.ContextCoordinateLineage TranslationContext TranslationCoordinate
translationLineage = Lineage.context-coordinate-lineage
  (λ
    { stateContext clinicalFactCoordinate → Provenance.inheritedCoordinate
    ; stateContext subjectAuthorshipCoordinate → Provenance.inheritedCoordinate
    ; stateContext historicalPathCoordinate → Provenance.inheritedCoordinate
    ; stateContext _ → Provenance.unresolvedLineage
    ; clinicalContext clinicalFactCoordinate → Provenance.inheritedCoordinate
    ; clinicalContext subjectAuthorshipCoordinate → Provenance.absentCoordinate
    ; clinicalContext historicalPathCoordinate → Provenance.absentCoordinate
    ; clinicalContext _ → Provenance.unresolvedLineage
    ; livedContext clinicalFactCoordinate → Provenance.inheritedCoordinate
    ; livedContext subjectAuthorshipCoordinate → Provenance.introducedCoordinate
    ; livedContext historicalPathCoordinate → Provenance.introducedCoordinate
    ; livedContext _ → Provenance.unresolvedLineage
    })

stateClinicalLineageReceipt :
  Lineage.LineageTransportReceipt translationLineage stateContext clinicalContext
stateClinicalLineageReceipt = Lineage.lineage-transport-receipt
  (λ
    { clinicalFactCoordinate → Provenance.preservesCoordinate
    ; subjectAuthorshipCoordinate → Provenance.erasesCoordinate
    ; historicalPathCoordinate → Provenance.erasesCoordinate
    ; _ → Provenance.unresolvedCoordinate
    })
  (λ
    { clinicalFactCoordinate → refl
    ; subjectAuthorshipCoordinate → refl
    ; historicalPathCoordinate → refl
    ; _ → refl
    })

clinicalLivedLineageReceipt :
  Lineage.LineageTransportReceipt translationLineage clinicalContext livedContext
clinicalLivedLineageReceipt = Lineage.lineage-transport-receipt
  (λ
    { clinicalFactCoordinate → Provenance.preservesCoordinate
    ; subjectAuthorshipCoordinate → Provenance.addsCoordinate
    ; historicalPathCoordinate → Provenance.addsCoordinate
    ; _ → Provenance.unresolvedCoordinate
    })
  (λ
    { clinicalFactCoordinate → refl
    ; subjectAuthorshipCoordinate → refl
    ; historicalPathCoordinate → refl
    ; _ → refl
    })

subjectAuthorshipAddedAfterErasureIsIntroduced :
  Lineage.lineageAt translationLineage livedContext subjectAuthorshipCoordinate
  ≡ Provenance.introducedCoordinate
subjectAuthorshipAddedAfterErasureIsIntroduced =
  Lineage.eraseThenAddAcrossContextsIsIntroduced
    stateClinicalLineageReceipt clinicalLivedLineageReceipt
    subjectAuthorshipCoordinate refl refl refl

historicalPathAddedAfterErasureIsIntroduced :
  Lineage.lineageAt translationLineage livedContext historicalPathCoordinate
  ≡ Provenance.introducedCoordinate
historicalPathAddedAfterErasureIsIntroduced =
  Lineage.eraseThenAddAcrossContextsIsIntroduced
    stateClinicalLineageReceipt clinicalLivedLineageReceipt
    historicalPathCoordinate refl refl refl

------------------------------------------------------------------------
-- Translation residuals seed backward contests.
------------------------------------------------------------------------

data TranslationResidual : Set where
  lexicalResidual
  useResidual
  subjectResidual
  communityResidual
  historyResidual
  legitimacyResidual
  materialResidual
  sovereigntyResidual
  : TranslationResidual

data ResidualFromStatus : TranslationStatus → TranslationResidual → Set where
  translatedLexicalResidual : ResidualFromStatus translatedWithResidual lexicalResidual
  translatedUseResidual : ResidualFromStatus translatedWithResidual useResidual
  erasedSubjectResidual : ResidualFromStatus erasedInTarget subjectResidual
  erasedCommunityResidual : ResidualFromStatus erasedInTarget communityResidual
  erasedHistoryResidual : ResidualFromStatus erasedInTarget historyResidual
  unresolvedLegitimacyResidual : ResidualFromStatus unresolvedTranslation legitimacyResidual
  translatedMaterialResidual : ResidualFromStatus translatedWithResidual materialResidual
  erasedSovereigntyResidual : ResidualFromStatus erasedInTarget sovereigntyResidual

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ValuePreservationPromotesSemanticIdentity : Set where

data ClinicalPreservationPromotesSubjectAuthority : Set where

data TranslationPromotesInvertibility : Set where

data TranslationPromotesSovereignPermission : Set where

valuePreservationDoesNotPromoteSemanticIdentity :
  ValuePreservationPromotesSemanticIdentity → ⊥
valuePreservationDoesNotPromoteSemanticIdentity ()

clinicalPreservationDoesNotPromoteSubjectAuthority :
  ClinicalPreservationPromotesSubjectAuthority → ⊥
clinicalPreservationDoesNotPromoteSubjectAuthority ()

translationDoesNotPromoteInvertibility : TranslationPromotesInvertibility → ⊥
translationDoesNotPromoteInvertibility ()

translationDoesNotPromoteSovereignPermission :
  TranslationPromotesSovereignPermission → ⊥
translationDoesNotPromoteSovereignPermission ()

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

record DrugCategoryMultiChartTranslationBoundary : Set where
  constructor drugCategoryMultiChartTranslationBoundary
  field
    translationEffectsAreCoordinateIndexed : Bool
    translationEffectsAreCoordinateIndexedIsTrue :
      translationEffectsAreCoordinateIndexed ≡ true
    clinicalFactCanSurviveWhileSubjectHistoryIsLost : Bool
    clinicalFactCanSurviveWhileSubjectHistoryIsLostIsTrue :
      clinicalFactCanSurviveWhileSubjectHistoryIsLost ≡ true
    eraseThenAddRestoresInheritedSubjectPosition : Bool
    eraseThenAddRestoresInheritedSubjectPositionIsFalse :
      eraseThenAddRestoresInheritedSubjectPosition ≡ false
    everyChartTranslationIsInvertible : Bool
    everyChartTranslationIsInvertibleIsFalse :
      everyChartTranslationIsInvertible ≡ false
    commercialTranslationPreservesIndigenousSovereigntyAutomatically : Bool
    commercialTranslationPreservesIndigenousSovereigntyAutomaticallyIsFalse :
      commercialTranslationPreservesIndigenousSovereigntyAutomatically ≡ false

canonicalDrugCategoryMultiChartTranslationBoundary :
  DrugCategoryMultiChartTranslationBoundary
canonicalDrugCategoryMultiChartTranslationBoundary =
  drugCategoryMultiChartTranslationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
