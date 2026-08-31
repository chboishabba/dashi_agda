module DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Authority

------------------------------------------------------------------------
-- PARTIAL CATEGORY OF CONTESTED-CONCEPT TRANSLATIONS
--
-- Raw ChartTranslation values are intentionally not assumed composable merely
-- because they concern the same policy domain.  A TranslationLeg pins an exact
-- source and target chart; TranslationPath then supplies identity, ordered
-- composition and retained coordinate-status history.
------------------------------------------------------------------------

record TranslationLeg
    (source target : Atlas.CategoryChart) : Set where
  constructor translationLeg
  field
    translation : Translation.ChartTranslation
    sourceMatches : Translation.sourceChart translation ≡ source
    targetMatches : Translation.targetChart translation ≡ target

open TranslationLeg public

data TranslationPath : Atlas.CategoryChart → Atlas.CategoryChart → Set where
  pathId : ∀ {chart} → TranslationPath chart chart
  pathStep :
    ∀ {source middle target} →
    TranslationLeg source middle →
    TranslationPath middle target →
    TranslationPath source target

appendPath :
  ∀ {first middle last} →
  TranslationPath first middle →
  TranslationPath middle last →
  TranslationPath first last
appendPath pathId right = right
appendPath (pathStep leg rest) right =
  pathStep leg (appendPath rest right)

appendPathLeftIdentity :
  ∀ {source target}
    (path : TranslationPath source target) →
  appendPath pathId path ≡ path
appendPathLeftIdentity path = refl

appendPathRightIdentity :
  ∀ {source target}
    (path : TranslationPath source target) →
  appendPath path pathId ≡ path
appendPathRightIdentity pathId = refl
appendPathRightIdentity (pathStep leg rest) =
  cong (pathStep leg) (appendPathRightIdentity rest)

appendPathAssociative :
  ∀ {a b c d}
    (first : TranslationPath a b)
    (second : TranslationPath b c)
    (third : TranslationPath c d) →
  appendPath (appendPath first second) third
  ≡ appendPath first (appendPath second third)
appendPathAssociative pathId second third = refl
appendPathAssociative (pathStep leg rest) second third =
  cong (pathStep leg) (appendPathAssociative rest second third)

------------------------------------------------------------------------
-- Exact status trace.  We deliberately retain every leg rather than collapse
-- erasure followed by addition into one surface flag; the canonical lineage
-- owner already establishes that erase -> add is introduced, not restored.
------------------------------------------------------------------------

statusTrace :
  ∀ {source target} →
  TranslationPath source target →
  Translation.TranslationCoordinate →
  List Translation.TranslationStatus
statusTrace pathId coordinate = []
statusTrace (pathStep leg rest) coordinate =
  Translation.coordinateStatus (translation leg) coordinate
  ∷ statusTrace rest coordinate

data StatusOccurs
    (status : Translation.TranslationStatus)
    : List Translation.TranslationStatus → Set where
  statusHere : ∀ {rest} → StatusOccurs status (status ∷ rest)
  statusThere :
    ∀ {head rest} →
    StatusOccurs status rest →
    StatusOccurs status (head ∷ rest)

data CoordinateResidualOccurs
    {source target : Atlas.CategoryChart}
    (path : TranslationPath source target)
    (coordinate : Translation.TranslationCoordinate) : Set where
  translatedResidualOccurs :
    StatusOccurs Translation.translatedWithResidual (statusTrace path coordinate) →
    CoordinateResidualOccurs path coordinate
  erasureOccurs :
    StatusOccurs Translation.erasedInTarget (statusTrace path coordinate) →
    CoordinateResidualOccurs path coordinate
  unresolvedOccurs :
    StatusOccurs Translation.unresolvedTranslation (statusTrace path coordinate) →
    CoordinateResidualOccurs path coordinate

------------------------------------------------------------------------
-- Concrete legs from the existing multi-chart owner.
------------------------------------------------------------------------

stateClinicalLeg :
  TranslationLeg Atlas.stateLegalChart Atlas.biomedicalChart
stateClinicalLeg = translationLeg Translation.stateToClinical refl refl

clinicalLivedLeg :
  TranslationLeg Atlas.biomedicalChart Atlas.livedSubjectChart
clinicalLivedLeg = translationLeg Translation.clinicalToLived refl refl

indigenousCommercialLeg :
  TranslationLeg Atlas.indigenousSovereignChart Atlas.commercialChart
indigenousCommercialLeg = translationLeg Translation.indigenousToCommercial refl refl

stateClinicalLivedPath :
  TranslationPath Atlas.stateLegalChart Atlas.livedSubjectChart
stateClinicalLivedPath =
  pathStep stateClinicalLeg (pathStep clinicalLivedLeg pathId)

stateClinicalLivedSubjectResidual :
  CoordinateResidualOccurs
    stateClinicalLivedPath Translation.subjectAuthorshipCoordinate
stateClinicalLivedSubjectResidual =
  erasureOccurs statusHere

stateClinicalLivedHistoryResidual :
  CoordinateResidualOccurs
    stateClinicalLivedPath Translation.historicalPathCoordinate
stateClinicalLivedHistoryResidual =
  erasureOccurs statusHere

stateClinicalLivedClinicalTraceIsPreserved :
  statusTrace stateClinicalLivedPath Translation.clinicalFactCoordinate
  ≡ Translation.preservedExactly ∷ Translation.preservedExactly ∷ []
stateClinicalLivedClinicalTraceIsPreserved = refl

------------------------------------------------------------------------
-- Consumer-indexed reversibility.  A path may be adequate/invertible on one
-- coordinate without being invertible on another.
------------------------------------------------------------------------

data CoordinatePreserved
    {source target : Atlas.CategoryChart}
    : TranslationPath source target →
      Translation.TranslationCoordinate → Set where
  preservedId :
    ∀ {chart coordinate} →
    CoordinatePreserved (pathId {chart}) coordinate
  preservedStep :
    ∀ {source middle target coordinate}
      {leg : TranslationLeg source middle}
      {rest : TranslationPath middle target} →
    Translation.coordinateStatus (translation leg) coordinate
      ≡ Translation.preservedExactly →
    CoordinatePreserved rest coordinate →
    CoordinatePreserved (pathStep leg rest) coordinate

clinicalFactPreservedAlongStateClinicalLived :
  CoordinatePreserved
    stateClinicalLivedPath Translation.clinicalFactCoordinate
clinicalFactPreservedAlongStateClinicalLived =
  preservedStep refl (preservedStep refl preservedId)

subjectAuthorshipNotPreservedAlongStateClinicalLived :
  CoordinatePreserved
    stateClinicalLivedPath Translation.subjectAuthorshipCoordinate → ⊥
subjectAuthorshipNotPreservedAlongStateClinicalLived
  (preservedStep () rest)

historicalPathNotPreservedAlongStateClinicalLived :
  CoordinatePreserved
    stateClinicalLivedPath Translation.historicalPathCoordinate → ⊥
historicalPathNotPreservedAlongStateClinicalLived
  (preservedStep () rest)

------------------------------------------------------------------------
-- Sovereign-authority-sensitive admission is a separate path predicate.
-- The synthetic sovereign -> commercial leg cannot inhabit it because the
-- translation owner explicitly erases sovereign authority.
------------------------------------------------------------------------

data SovereignAuthorityPreserved
    {source target : Atlas.CategoryChart}
    : TranslationPath source target → Set where
  sovereignId :
    ∀ {chart} → SovereignAuthorityPreserved (pathId {chart})
  sovereignStep :
    ∀ {source middle target}
      {leg : TranslationLeg source middle}
      {rest : TranslationPath middle target} →
    Translation.coordinateStatus
      (translation leg) Translation.sovereignAuthorityCoordinate
      ≡ Translation.preservedExactly →
    SovereignAuthorityPreserved rest →
    SovereignAuthorityPreserved (pathStep leg rest)

indigenousCommercialPath :
  TranslationPath Atlas.indigenousSovereignChart Atlas.commercialChart
indigenousCommercialPath = pathStep indigenousCommercialLeg pathId

indigenousCommercialPathCannotPreserveSovereignAuthority :
  SovereignAuthorityPreserved indigenousCommercialPath → ⊥
indigenousCommercialPathCannotPreserveSovereignAuthority
  (sovereignStep () rest)

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ClinicalCoordinateInvertibilityPromotesGlobalInvertibility : Set where

data PathCompositionPromotesAuthority : Set where

data SameEndpointPromotesSameTranslationHistory : Set where

clinicalCoordinateDoesNotPromoteGlobalInvertibility :
  ClinicalCoordinateInvertibilityPromotesGlobalInvertibility → ⊥
clinicalCoordinateDoesNotPromoteGlobalInvertibility ()

pathCompositionDoesNotPromoteAuthority :
  PathCompositionPromotesAuthority → ⊥
pathCompositionDoesNotPromoteAuthority ()

sameEndpointDoesNotPromoteSameHistory :
  SameEndpointPromotesSameTranslationHistory → ⊥
sameEndpointDoesNotPromoteSameHistory ()

record DrugCategoryPartialTranslationPathBoundary : Set where
  constructor drugCategoryPartialTranslationPathBoundary
  field
    pathsHaveIdentityAndAssociativeComposition : Bool
    pathsHaveIdentityAndAssociativeCompositionIsTrue :
      pathsHaveIdentityAndAssociativeComposition ≡ true
    coordinateStatusHistoryIsRetained : Bool
    coordinateStatusHistoryIsRetainedIsTrue :
      coordinateStatusHistoryIsRetained ≡ true
    oneCoordinateCanBePreservedWhileAnotherIsLost : Bool
    oneCoordinateCanBePreservedWhileAnotherIsLostIsTrue :
      oneCoordinateCanBePreservedWhileAnotherIsLost ≡ true
    sovereignCommercialTranslationAutomaticallyPreservesAuthority : Bool
    sovereignCommercialTranslationAutomaticallyPreservesAuthorityIsFalse :
      sovereignCommercialTranslationAutomaticallyPreservesAuthority ≡ false
    compositionCreatesMissingAuthority : Bool
    compositionCreatesMissingAuthorityIsFalse :
      compositionCreatesMissingAuthority ≡ false

canonicalDrugCategoryPartialTranslationPathBoundary :
  DrugCategoryPartialTranslationPathBoundary
canonicalDrugCategoryPartialTranslationPathBoundary =
  drugCategoryPartialTranslationPathBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
