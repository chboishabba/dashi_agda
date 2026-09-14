module DASHI.Law.AustralianFamilyReportWriterIntegrityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Core.MeasurementAdministrationComparabilityExact as Measurement
import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry
import DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceExact as Standard25

------------------------------------------------------------------------
-- AUSTRALIAN FAMILY-REPORT WRITER INTEGRITY ADAPTER
--
-- Composes generic expert-production, measurement-comparability, source-
-- genealogy/inference-ancestry, and the source-bound Standard 25 child.
--
-- Each source coordinate below has one PRIMARY routing axis only.  This is a
-- compact dependency map, not a claim that a numbered standard has only one
-- meaning or that the mapped axis exhausts professional/legal obligations.
--
-- Citation/source location supplies a comparator.  Case application, breach,
-- admissibility, causation, professional discipline and judicial findings remain
-- separate payments.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Parent reuse: no parallel generic ontology.
------------------------------------------------------------------------

parentProductionBoundary : Expert.ExpertProductionBoundary
parentProductionBoundary = Expert.canonicalExpertProductionBoundary

parentMeasurementBoundary : Measurement.MeasurementComparabilityBoundary
parentMeasurementBoundary = Measurement.canonicalMeasurementComparabilityBoundary

parentAncestryBoundary : Ancestry.ExpertInferenceAncestryBoundary
parentAncestryBoundary = Ancestry.canonicalExpertInferenceAncestryBoundary

parentStandard25Boundary : Standard25.Standard25Boundary
parentStandard25Boundary = Standard25.canonicalStandard25Boundary

------------------------------------------------------------------------
-- Source attribution.
------------------------------------------------------------------------

australianFamilyAssessmentStandardsSource : Attribution.AttributedSource
australianFamilyAssessmentStandardsSource =
  Standard25.australianFamilyAssessmentStandardsSource

currentFamilyViolenceBestPracticePrinciplesSource : Attribution.AttributedSource
currentFamilyViolenceBestPracticePrinciplesSource = Attribution.mkNoDOISource
  "Federal Circuit and Family Court of Australia"
  "Family Violence Best Practice Principles"
  "Fifth Edition"
  "2023"
  "https://www.fcfcoa.gov.au/pubs/fl/fvbpp"
  Attribution.technicalStandardSource
  "current Court guidance supporting the bounded risk-information and specialist-family-violence-knowledge coordinates, including expectations for private family report writers; does not rewrite the historical 2015 Standard 27 citation or establish case-specific breach"
  Attribution.publicAttribution

familyReportIntegritySourceAtlas : Attribution.AttributedSourceAtlas
familyReportIntegritySourceAtlas = Attribution.mkSourceAtlas
  "Australian family-report writer integrity source atlas"
  "DASHI.Law.AustralianFamilyReportWriterIntegrityExact"
  (australianFamilyAssessmentStandardsSource
    ∷ currentFamilyViolenceBestPracticePrinciplesSource
    ∷ [])
  "2015 family-assessment Standards plus current Fifth Edition family-violence guidance; source identity and chronology retained; no automatic legal/professional finding"

------------------------------------------------------------------------
-- Source coordinates and primary routing axes.
------------------------------------------------------------------------

data FamilyAssessmentStandardCoordinate : Set where
  standard8 : FamilyAssessmentStandardCoordinate
  standard10 : FamilyAssessmentStandardCoordinate
  standard11 : FamilyAssessmentStandardCoordinate
  standard12 : FamilyAssessmentStandardCoordinate
  standard13 : FamilyAssessmentStandardCoordinate
  standard15 : FamilyAssessmentStandardCoordinate
  standard23 : FamilyAssessmentStandardCoordinate
  standard24 : FamilyAssessmentStandardCoordinate
  standard25 : FamilyAssessmentStandardCoordinate
  standard26 : FamilyAssessmentStandardCoordinate
  standard27 : FamilyAssessmentStandardCoordinate
  standard28 : FamilyAssessmentStandardCoordinate
  standard29 : FamilyAssessmentStandardCoordinate
  currentFamilyViolencePrinciple6 : FamilyAssessmentStandardCoordinate

data FamilyAssessmentIntegrityAxis : Set where
  exParteIntegrity : FamilyAssessmentIntegrityAxis
  dataGatheringIndependence : FamilyAssessmentIntegrityAxis
  methodologicalAdequacy : FamilyAssessmentIntegrityAxis
  psychometricUseAdequacy : FamilyAssessmentIntegrityAxis
  forensicTherapeuticRoleSeparation : FamilyAssessmentIntegrityAxis
  adverseMaterialResponse : FamilyAssessmentIntegrityAxis
  tentativeHypothesisDiscipline : FamilyAssessmentIntegrityAxis
  recommendationTiming : FamilyAssessmentIntegrityAxis
  priorOpinionIndependence : FamilyAssessmentIntegrityAxis
  riskInformationCoverage : FamilyAssessmentIntegrityAxis
  familyViolenceAssessment : FamilyAssessmentIntegrityAxis
  dataInferenceOpinionTraceability : FamilyAssessmentIntegrityAxis
  limitationsAndAbstention : FamilyAssessmentIntegrityAxis

standardAxis : FamilyAssessmentStandardCoordinate → FamilyAssessmentIntegrityAxis
standardAxis standard8 = exParteIntegrity
standardAxis standard10 = dataGatheringIndependence
standardAxis standard11 = methodologicalAdequacy
standardAxis standard12 = psychometricUseAdequacy
standardAxis standard13 = forensicTherapeuticRoleSeparation
standardAxis standard15 = adverseMaterialResponse
standardAxis standard23 = tentativeHypothesisDiscipline
standardAxis standard24 = recommendationTiming
standardAxis standard25 = priorOpinionIndependence
standardAxis standard26 = riskInformationCoverage
standardAxis standard27 = familyViolenceAssessment
standardAxis standard28 = dataInferenceOpinionTraceability
standardAxis standard29 = limitationsAndAbstention
standardAxis currentFamilyViolencePrinciple6 = riskInformationCoverage

------------------------------------------------------------------------
-- Chronology / same-source discipline.
--
-- Standard 27 in the 2015 document names Family Violence Best Practice
-- Principles edition 3.1 (2013).  The Court now publishes a Fifth Edition.
-- The current source may inform a current adapter, but it cannot silently alter
-- what the historical 2015 source literally referenced.
------------------------------------------------------------------------

data FamilyViolenceGuidanceEdition : Set where
  edition3_1_2013 : FamilyViolenceGuidanceEdition
  fifthEditionCurrentPublication : FamilyViolenceGuidanceEdition

historicalStandard27ReferencedEdition : FamilyViolenceGuidanceEdition
historicalStandard27ReferencedEdition = edition3_1_2013

currentPublishedFamilyViolenceEdition : FamilyViolenceGuidanceEdition
currentPublishedFamilyViolenceEdition = fifthEditionCurrentPublication

------------------------------------------------------------------------
-- Thin application receipt.  Evidence of conduct and authoritative findings
-- stay external to this source-routing object.
------------------------------------------------------------------------

record FamilyAssessmentIntegrityReceipt : Set where
  constructor familyAssessmentIntegrityReceipt
  field
    sourceCoordinate : FamilyAssessmentStandardCoordinate
    primaryAxis : FamilyAssessmentIntegrityAxis
    manifestationEvidenceReference : String
    applicationReasonReference : String
    sourceComparatorPaid : Bool
    caseApplicationPaid : Bool
    authoritativeBreachFindingPaid : Bool

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SourceComparatorAutomaticallyEstablishesBreach : Set where
data CurrentGuidanceAutomaticallyRewritesHistoricalCitation : Set where
data PrimaryAxisAutomaticallyExhaustsStandard : Set where
data CurrentRiskGuidanceAutomaticallyProvesCaseRisk : Set where
data PrivateReportWriterAutomaticallyCourtEmployee : Set where

sourceComparatorDoesNotEstablishBreach :
  SourceComparatorAutomaticallyEstablishesBreach → ⊥
sourceComparatorDoesNotEstablishBreach ()

currentGuidanceDoesNotRewriteHistoricalCitation :
  CurrentGuidanceAutomaticallyRewritesHistoricalCitation → ⊥
currentGuidanceDoesNotRewriteHistoricalCitation ()

primaryAxisDoesNotAutomaticallyExhaustStandard :
  PrimaryAxisAutomaticallyExhaustsStandard → ⊥
primaryAxisDoesNotAutomaticallyExhaustStandard ()

currentRiskGuidanceDoesNotAutomaticallyProveCaseRisk :
  CurrentRiskGuidanceAutomaticallyProvesCaseRisk → ⊥
currentRiskGuidanceDoesNotAutomaticallyProveCaseRisk ()

privateReportWriterDoesNotAutomaticallyBecomeCourtEmployee :
  PrivateReportWriterAutomaticallyCourtEmployee → ⊥
privateReportWriterDoesNotAutomaticallyBecomeCourtEmployee ()

record AustralianFamilyReportWriterBoundary : Set where
  constructor australianFamilyReportWriterBoundary
  field
    genericProductionParentReused : Bool
    genericMeasurementParentReused : Bool
    genericAncestryParentReused : Bool
    standard25ParentReused : Bool
    currentStandardsPageStructuralCaveatRetained : Bool
    currentFamilyViolencePrinciple6Located : Bool
    privateWriterRiskInformationExpectationLocated : Bool
    privateWriterSpecialistFamilyViolenceExpectationLocated : Bool
    historicalStandard27ReferenceIsNotCurrentFifthEdition : Bool
    sourceComparatorEstablishesBreach : Bool
    currentGuidanceRewritesHistoricalCitation : Bool
    onePrimaryAxisExhaustsEachStandard : Bool
    currentRiskGuidanceProvesCaseRisk : Bool
    sourceCitationCreatesLegalAuthority : Bool

open AustralianFamilyReportWriterBoundary public

canonicalAustralianFamilyReportWriterBoundary : AustralianFamilyReportWriterBoundary
canonicalAustralianFamilyReportWriterBoundary =
  australianFamilyReportWriterBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
