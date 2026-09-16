module DASHI.Education.DigitalESDStudyClaimMethodBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling

------------------------------------------------------------------------
-- THIN METHOD BRIDGE
--
-- The manuscript's existing 19-coordinate schema remains canonical.  This
-- bridge appends one review-level coordinate containing the structured
-- study-claim ceiling profile.  It does not duplicate the base methodology or
-- the generic experimental/statistical theories.
------------------------------------------------------------------------

baseMethodBoundary : Method.MethodologyBoundary
baseMethodBoundary = Method.canonicalMethodologyBoundary

studyClaimCeilingBoundary : Ceiling.StudyClaimCeilingBoundary
studyClaimCeilingBoundary = Ceiling.canonicalStudyClaimCeilingBoundary

baseExtractionCoordinateCount : Nat
baseExtractionCoordinateCount = Method.extractionCoordinateCount

effectiveExtractionCoordinateCount : Nat
effectiveExtractionCoordinateCount = 20

record StudyClaimMethodBoundary : Set where
  constructor study-claim-method-boundary
  field
    baseMethodRetained : Bool
    baseMethodRetainedIsTrue : baseMethodRetained ≡ true
    baseNineteenCoordinatesRetained : Bool
    baseNineteenCoordinatesRetainedIsTrue :
      baseNineteenCoordinatesRetained ≡ true
    studyClaimCeilingRequired : Bool
    studyClaimCeilingRequiredIsTrue : studyClaimCeilingRequired ≡ true
    effectiveTwentyCoordinateExtraction : Bool
    effectiveTwentyCoordinateExtractionIsTrue :
      effectiveTwentyCoordinateExtraction ≡ true
    unreportedQuantitiesMayBeFilledFromNarrativeConfidence : Bool
    unreportedQuantitiesMayBeFilledFromNarrativeConfidenceIsFalse :
      unreportedQuantitiesMayBeFilledFromNarrativeConfidence ≡ false
    strongerImplicationMayBePromotedWithoutReceipt : Bool
    strongerImplicationMayBePromotedWithoutReceiptIsFalse :
      strongerImplicationMayBePromotedWithoutReceipt ≡ false

open StudyClaimMethodBoundary public

canonicalStudyClaimMethodBoundary : StudyClaimMethodBoundary
canonicalStudyClaimMethodBoundary =
  study-claim-method-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

studyClaimMethodReading : String
studyClaimMethodReading =
  "The digital-ESD review retains the existing 19-coordinate manuscript extraction schema and adds one structured study-claim-ceiling coordinate, yielding 20 top-level extraction coordinates. The appended profile retains design type, source population, reported/enrolled n, analysis n, allocation, comparator, measurement validity, attrition/missingness, confounding control, implementation fidelity, multiplicity, effect size, uncertainty/confidence-interval semantics, time horizon, external-validity domain, participant role and the strongest implication the study can support. Missing quantities are not reconstructed from prose confidence, and stronger causal, mechanistic, transport, prevalence, practice or system-transformation claims require independent receipts."
