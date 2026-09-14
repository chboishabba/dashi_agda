module DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceExact as Standard25
import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry
import DASHI.Core.AttributedSourceCore as Attribution

standard25SourceIsNonPromoting :
  Attribution.citationCreatesAuthority Standard25.australianFamilyAssessmentStandardsSource ≡ false
standard25SourceIsNonPromoting =
  Attribution.citationCreatesAuthorityIsFalse Standard25.australianFamilyAssessmentStandardsSource

parentAncestryBoundaryIsReused : Ancestry.ExpertInferenceAncestryBoundary
parentAncestryBoundaryIsReused = Standard25.parentAncestryBoundary

beforeOwnViewIsIndependenceRiskState :
  Standard25.standard25Disposition Ancestry.beforeOwnViewFormed ≡
  Standard25.independenceRiskFlagged
beforeOwnViewIsIndependenceRiskState = refl

afterOwnViewIsLaterComparativeReadingState :
  Standard25.standard25Disposition Ancestry.afterOwnViewFormed ≡
  Standard25.laterComparativeReading

afterOwnViewIsLaterComparativeReadingState = refl

exposureDoesNotBecomeCausalDependence :
  Standard25.Standard25ExposureAutomaticallyProvesCausalDependence → ⊥
exposureDoesNotBecomeCausalDependence =
  Standard25.standard25ExposureDoesNotProveCausalDependence

laterReadingDoesNotProveIndependence :
  Standard25.Standard25LaterReadingAutomaticallyProvesIndependence → ⊥
laterReadingDoesNotProveIndependence =
  Standard25.standard25LaterReadingDoesNotProveIndependence

citationDoesNotEstablishBreach :
  Standard25.Standard25CitationAutomaticallyEstablishesBreach → ⊥
citationDoesNotEstablishBreach =
  Standard25.standard25CitationDoesNotEstablishBreach

currentPageKeepsStructuralCaveat :
  Standard25.currentPublicationStructuralCaveatRetained
  Standard25.canonicalStandard25Boundary ≡ true
currentPageKeepsStructuralCaveat = refl

standard25IsNotGenericDependencyPaper :
  Standard25.standard25SourceIsDistinctFromDependencySource
  Standard25.canonicalStandard25Boundary ≡ true
standard25IsNotGenericDependencyPaper = refl
