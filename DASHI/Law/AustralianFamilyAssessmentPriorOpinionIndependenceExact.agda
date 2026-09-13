module DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry

------------------------------------------------------------------------
-- AUSTRALIAN FAMILY ASSESSMENT STANDARD 25: PRIOR OPINION INDEPENDENCE
--
-- Thin Australian adapter over the generic expert-inference ancestry owner.
-- Source role is deliberately narrow: the 2015 Court-published Standards pay a
-- professional-practice comparator for timing of reading similar prior family
-- assessments.  They do not, by citation alone, establish misconduct, legal
-- breach, admissibility, causal influence, or factual dependence in a case.
--
-- The current FCFCOA publication page itself says the Standards were developed
-- before the present Court structure and that the current issue does not reflect
-- recent structural changes.  That caveat is retained explicitly below.
------------------------------------------------------------------------

australianFamilyAssessmentStandardsSource : Attribution.AttributedSource
australianFamilyAssessmentStandardsSource = Attribution.mkNoDOISource
  "Family Court of Australia; Federal Circuit Court of Australia; Family Court of Western Australia"
  "Australian Standards of Practice for Family Assessments and Reporting"
  "Federal Circuit and Family Court of Australia publication page"
  "2015"
  "https://www.fcfcoa.gov.au/fl/pubs/aus-standards-practice-2015"
  Attribution.technicalStandardSource
  "Standard 25 supports a bounded practice distinction concerning when similar prior family-assessment evaluations are read, reasons for necessary early reading, and later comparative reading after an assessor has formulated an own view; source citation does not establish breach, causal influence, admissibility, or legal authority"
  Attribution.publicAttribution

standard25SourceAtlas : Attribution.AttributedSourceAtlas
standard25SourceAtlas = Attribution.mkSourceAtlas
  "Australian family-assessment Standard 25 source atlas"
  "DASHI.Law.AustralianFamilyAssessmentPriorOpinionIndependenceExact"
  (australianFamilyAssessmentStandardsSource ∷ [])
  "source-bounded Standard 25 adapter only; generic dependency scholarship and case-specific application remain separate sources/payments"

------------------------------------------------------------------------
-- Exact parent reuse: no parallel dependency or inference-ancestry ontology.
------------------------------------------------------------------------

parentAncestryBoundary : Ancestry.ExpertInferenceAncestryBoundary
parentAncestryBoundary = Ancestry.canonicalExpertInferenceAncestryBoundary

parentStructuralPrecedent : Ancestry.ParentStructuralPrecedent
parentStructuralPrecedent = Ancestry.parentStructuralPrecedent

------------------------------------------------------------------------
-- Timing-sensitive practice disposition.
--
-- This is not a breach classifier.  It only records the source-bounded practice
-- state needed by a later application layer.
------------------------------------------------------------------------

data Standard25Disposition : Set where
  independenceRiskFlagged : Standard25Disposition
  laterComparativeReading : Standard25Disposition
  timingUnresolved : Standard25Disposition

standard25Disposition :
  Ancestry.PriorOpinionExposureTiming → Standard25Disposition
standard25Disposition Ancestry.beforeOwnViewFormed = independenceRiskFlagged
standard25Disposition Ancestry.afterOwnViewFormed = laterComparativeReading
standard25Disposition Ancestry.exposureTimingUnresolved = timingUnresolved

record Standard25PracticeReceipt : Set where
  constructor standard25PracticeReceipt
  field
    exposure : Ancestry.PriorOpinionExposureReceipt
    disposition : Standard25Disposition
    necessaryEarlyReadingReasonRecorded : Bool
    reportDelineatesReason : Bool
    ownViewFormedBeforeComparativeReading : Bool

------------------------------------------------------------------------
-- WrongType / authority firewalls.
------------------------------------------------------------------------

data Standard25ExposureAutomaticallyProvesCausalDependence : Set where
data Standard25LaterReadingAutomaticallyProvesIndependence : Set where
data Standard25CitationAutomaticallyEstablishesBreach : Set where
data Standard25AutomaticallyControlsAdmissibility : Set where
data Standard25AutomaticallyCreatesLegalAuthority : Set where

standard25ExposureDoesNotProveCausalDependence :
  Standard25ExposureAutomaticallyProvesCausalDependence → ⊥
standard25ExposureDoesNotProveCausalDependence ()

standard25LaterReadingDoesNotProveIndependence :
  Standard25LaterReadingAutomaticallyProvesIndependence → ⊥
standard25LaterReadingDoesNotProveIndependence ()

standard25CitationDoesNotEstablishBreach :
  Standard25CitationAutomaticallyEstablishesBreach → ⊥
standard25CitationDoesNotEstablishBreach ()

standard25DoesNotAutomaticallyControlAdmissibility :
  Standard25AutomaticallyControlsAdmissibility → ⊥
standard25DoesNotAutomaticallyControlAdmissibility ()

standard25DoesNotAutomaticallyCreateLegalAuthority :
  Standard25AutomaticallyCreatesLegalAuthority → ⊥
standard25DoesNotAutomaticallyCreateLegalAuthority ()

------------------------------------------------------------------------
-- Source/status boundary.
------------------------------------------------------------------------

record Standard25Boundary : Set where
  constructor standard25Boundary
  field
    standard25PracticeComparatorLocated : Bool
    earlySimilarEvaluationReadingMayCompromiseIndependence : Bool
    necessaryEarlyReadingMayOccur : Bool
    necessaryEarlyReadingReasonShouldBeDelineated : Bool
    laterComparativeReadingAfterOwnViewRecommended : Bool
    currentPublicationStructuralCaveatRetained : Bool
    standard25SourceIsDistinctFromDependencySource : Bool
    citationEstablishesBreach : Bool
    exposureEstablishesCausalDependence : Bool
    laterReadingEstablishesIndependence : Bool
    citationCreatesLegalAuthority : Bool

open Standard25Boundary public

canonicalStandard25Boundary : Standard25Boundary
canonicalStandard25Boundary = standard25Boundary
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
