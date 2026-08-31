module DASHI.Governance.DrugCategoryTranslationPathResidueExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas

------------------------------------------------------------------------
-- TRANSLATION PATH RESIDUE
--
-- Distinct chart-translation histories may end at the same visible category
-- surface while retaining different authority/history/material residuals.
------------------------------------------------------------------------

data TranslationPathState : Set where
  stateClinicalLivedPath
  stateCommercialLivedPath
  stateSovereignCommunityPath
  : TranslationPathState

data VisibleDestination : Set where
  positivePsychedelicLegibility : VisibleDestination

data PathResidueCode : Set where
  clinicalSubjectResidue
  commercialExtractionResidue
  sovereignCommunityResidue
  : PathResidueCode

visibleDestination : TranslationPathState → VisibleDestination
visibleDestination _ = positivePsychedelicLegibility

pathResidue : TranslationPathState → PathResidueCode
pathResidue stateClinicalLivedPath = clinicalSubjectResidue
pathResidue stateCommercialLivedPath = commercialExtractionResidue
pathResidue stateSovereignCommunityPath = sovereignCommunityResidue

clinicalCommercialResiduesDiffer :
  pathResidue stateClinicalLivedPath
  ≡ pathResidue stateCommercialLivedPath → ⊥
clinicalCommercialResiduesDiffer ()

sameVisibleDestinationCannotRecoverTranslationPathResidue :
  INF.FactorsThrough visibleDestination pathResidue → ⊥
sameVisibleDestinationCannotRecoverTranslationPathResidue =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      stateClinicalLivedPath
      stateCommercialLivedPath
      refl
      clinicalCommercialResiduesDiffer)

------------------------------------------------------------------------
-- Path order / route kind is not erased by final positive legibility.
------------------------------------------------------------------------

data TranslationRouteKind : Set where
  medicalisationRoute
  commercialisationRoute
  sovereignCommunityRoute
  : TranslationRouteKind

routeKind : TranslationPathState → TranslationRouteKind
routeKind stateClinicalLivedPath = medicalisationRoute
routeKind stateCommercialLivedPath = commercialisationRoute
routeKind stateSovereignCommunityPath = sovereignCommunityRoute

data PositiveSurfacePromotesSameHistory : Set where

data PositiveSurfacePromotesSameAuthority : Set where

data MedicalAndCommercialRoutePromotesSemanticIdentity : Set where

positiveSurfaceDoesNotPromoteSameHistory :
  PositiveSurfacePromotesSameHistory → ⊥
positiveSurfaceDoesNotPromoteSameHistory ()

positiveSurfaceDoesNotPromoteSameAuthority :
  PositiveSurfacePromotesSameAuthority → ⊥
positiveSurfaceDoesNotPromoteSameAuthority ()

medicalCommercialRoutesDoNotPromoteSemanticIdentity :
  MedicalAndCommercialRoutePromotesSemanticIdentity → ⊥
medicalCommercialRoutesDoNotPromoteSemanticIdentity ()

translationBoundary : Translation.DrugCategoryMultiChartTranslationBoundary
translationBoundary = Translation.canonicalDrugCategoryMultiChartTranslationBoundary

atlasBoundary : Atlas.ContestedDrugCategoryAtlasBoundary
atlasBoundary = Atlas.canonicalContestedDrugCategoryAtlasBoundary

record DrugCategoryTranslationPathResidueBoundary : Set where
  constructor drugCategoryTranslationPathResidueBoundary
  field
    sameDestinationCanHideDifferentTranslationHistory : Bool
    sameDestinationCanHideDifferentTranslationHistoryIsTrue :
      sameDestinationCanHideDifferentTranslationHistory ≡ true
    samePositiveSurfaceDeterminesSameAuthority : Bool
    samePositiveSurfaceDeterminesSameAuthorityIsFalse :
      samePositiveSurfaceDeterminesSameAuthority ≡ false
    medicalisationAndCommercialisationAreSameTranslation : Bool
    medicalisationAndCommercialisationAreSameTranslationIsFalse :
      medicalisationAndCommercialisationAreSameTranslation ≡ false
    finalCategorySurfaceErasesPathResidue : Bool
    finalCategorySurfaceErasesPathResidueIsFalse :
      finalCategorySurfaceErasesPathResidue ≡ false

canonicalDrugCategoryTranslationPathResidueBoundary :
  DrugCategoryTranslationPathResidueBoundary
canonicalDrugCategoryTranslationPathResidueBoundary =
  drugCategoryTranslationPathResidueBoundary
    true refl
    false refl
    false refl
    false refl
