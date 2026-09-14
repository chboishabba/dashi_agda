module DASHI.Law.AustralianFamilyReportWriterIntegrityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianFamilyReportWriterIntegrityExact as AU
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Core.MeasurementAdministrationComparabilityExact as Measurement
import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry
import DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceExact as Standard25
import DASHI.Core.AttributedSourceCore as Attribution

productionParentReused : Expert.ExpertProductionBoundary
productionParentReused = AU.parentProductionBoundary

measurementParentReused : Measurement.MeasurementComparabilityBoundary
measurementParentReused = AU.parentMeasurementBoundary

ancestryParentReused : Ancestry.ExpertInferenceAncestryBoundary
ancestryParentReused = AU.parentAncestryBoundary

standard25ParentReused : Standard25.Standard25Boundary
standard25ParentReused = AU.parentStandard25Boundary

standard12MapsPsychometricAxis :
  AU.standardAxis AU.standard12 ≡ AU.psychometricUseAdequacy
standard12MapsPsychometricAxis = refl

standard25MapsPriorOpinionAxis :
  AU.standardAxis AU.standard25 ≡ AU.priorOpinionIndependence
standard25MapsPriorOpinionAxis = refl

standard28MapsInferenceTraceability :
  AU.standardAxis AU.standard28 ≡ AU.dataInferenceOpinionTraceability
standard28MapsInferenceTraceability = refl

standard29MapsLimitationsAndAbstention :
  AU.standardAxis AU.standard29 ≡ AU.limitationsAndAbstention
standard29MapsLimitationsAndAbstention = refl

currentFamilyViolencePrinciple6MapsRiskInformation :
  AU.standardAxis AU.currentFamilyViolencePrinciple6 ≡ AU.riskInformationCoverage
currentFamilyViolencePrinciple6MapsRiskInformation = refl

historicalStandard27ReferenceRemainsDistinct :
  AU.historicalStandard27ReferenceIsNotCurrentFifthEdition
    AU.canonicalAustralianFamilyReportWriterBoundary ≡ true
historicalStandard27ReferenceRemainsDistinct = refl

standardsCitationIsNonPromoting :
  Attribution.citationCreatesAuthority AU.australianFamilyAssessmentStandardsSource ≡ false
standardsCitationIsNonPromoting =
  Attribution.citationCreatesAuthorityIsFalse AU.australianFamilyAssessmentStandardsSource

currentFamilyViolenceCitationIsNonPromoting :
  Attribution.citationCreatesAuthority AU.currentFamilyViolenceBestPracticePrinciplesSource ≡ false
currentFamilyViolenceCitationIsNonPromoting =
  Attribution.citationCreatesAuthorityIsFalse AU.currentFamilyViolenceBestPracticePrinciplesSource

sourceComparatorDoesNotEstablishBreach :
  AU.SourceComparatorAutomaticallyEstablishesBreach → ⊥
sourceComparatorDoesNotEstablishBreach =
  AU.sourceComparatorDoesNotEstablishBreach

currentGuidanceDoesNotRewriteHistoricalSource :
  AU.CurrentGuidanceAutomaticallyRewritesHistoricalCitation → ⊥
currentGuidanceDoesNotRewriteHistoricalSource =
  AU.currentGuidanceDoesNotRewriteHistoricalCitation
