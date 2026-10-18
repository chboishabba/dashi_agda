module DASHI.Education.DigitalESDStudyClaimMethodBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF

------------------------------------------------------------------------
-- THIN METHOD BRIDGE
--
-- The 20-coordinate extraction remains stable.  Predicate-level result
-- auditing, intersectional absence and material/environmental substrate are
-- mandatory overlays rather than silently adding more flat columns.
------------------------------------------------------------------------

baseMethodBoundary : Method.MethodologyBoundary
baseMethodBoundary = Method.canonicalMethodologyBoundary

studyClaimCeilingBoundary : Ceiling.StudyClaimCeilingBoundary
studyClaimCeilingBoundary = Ceiling.canonicalStudyClaimCeilingBoundary

baseExtractionCoordinateCount : Nat
baseExtractionCoordinateCount = Method.extractionCoordinateCount

effectiveExtractionCoordinateCount : Nat
effectiveExtractionCoordinateCount = 20

intersectionalAbsenceQuestionCount : Nat
intersectionalAbsenceQuestionCount = Absence.absenceAuditQuestionCount

materialAuditQuestionCount : Nat
materialAuditQuestionCount = Material.materialAuditQuestionCount

predicateNormalFormBoundary : PNF.PredicateNormalFormBoundary
predicateNormalFormBoundary = PNF.canonicalPredicateNormalFormBoundary

record StudyClaimMethodBoundary : Set where
  constructor study-claim-method-boundary
  field
    baseMethodRetained : Bool
    baseMethodRetainedIsTrue : baseMethodRetained ≡ true
    baseNineteenCoordinatesRetained : Bool
    baseNineteenCoordinatesRetainedIsTrue : baseNineteenCoordinatesRetained ≡ true
    studyClaimCeilingRequired : Bool
    studyClaimCeilingRequiredIsTrue : studyClaimCeilingRequired ≡ true
    effectiveTwentyCoordinateExtraction : Bool
    effectiveTwentyCoordinateExtractionIsTrue : effectiveTwentyCoordinateExtraction ≡ true
    predicateLevelResultAuditRequired : Bool
    predicateLevelResultAuditRequiredIsTrue : predicateLevelResultAuditRequired ≡ true
    intersectionalAbsenceAuditRequired : Bool
    intersectionalAbsenceAuditRequiredIsTrue : intersectionalAbsenceAuditRequired ≡ true
    materialEnvironmentalAuditRequired : Bool
    materialEnvironmentalAuditRequiredIsTrue : materialEnvironmentalAuditRequired ≡ true
    qualitativeAndReviewClaimKindsRetained : Bool
    qualitativeAndReviewClaimKindsRetainedIsTrue : qualitativeAndReviewClaimKindsRetained ≡ true
    unreportedQuantitiesMayBeFilledFromNarrativeConfidence : Bool
    unreportedQuantitiesMayBeFilledFromNarrativeConfidenceIsFalse : unreportedQuantitiesMayBeFilledFromNarrativeConfidence ≡ false
    strongerClaimMayBePromotedWithoutReceipt : Bool
    strongerClaimMayBePromotedWithoutReceiptIsFalse : strongerClaimMayBePromotedWithoutReceipt ≡ false
    absentGroupMayBeInferredFromUnreportedDemographics : Bool
    absentGroupMayBeInferredFromUnreportedDemographicsIsFalse : absentGroupMayBeInferredFromUnreportedDemographics ≡ false
    genericInfrastructureAverageMayBecomeDeploymentFootprint : Bool
    genericInfrastructureAverageMayBecomeDeploymentFootprintIsFalse : genericInfrastructureAverageMayBecomeDeploymentFootprint ≡ false

open StudyClaimMethodBoundary public

canonicalStudyClaimMethodBoundary : StudyClaimMethodBoundary
canonicalStudyClaimMethodBoundary =
  study-claim-method-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

studyClaimMethodReading : String
studyClaimMethodReading =
  "The digital-ESD review retains the existing 19-coordinate manuscript extraction schema plus one structured study-claim-ceiling coordinate, yielding 20 top-level extraction coordinates. Every admitted study is additionally audited at three non-flat overlays: (1) a paid Predicate Normal Form result assertion exposing population/context/intervention/comparator/outcome/time and inferential force; (2) a 'who is not at the table?' intersectional absence audit covering realised sample, structural exclusion, disability/access, disclosure, affected-but-unsampled parties, interpretation and authority; and (3) a material/environmental substrate audit covering chips/devices, compute/data centres, electricity, water, embodied materials, service life, repair/reuse and e-waste. These overlays do not fabricate demographics or deployment footprints when sources do not report them. Missing statistical quantities remain unfilled, and stronger causal, mechanistic, transport, prevalence, practice or system-transformation claims require independent receipts."