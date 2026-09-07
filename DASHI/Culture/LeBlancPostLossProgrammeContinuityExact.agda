module DASHI.Culture.LeBlancPostLossProgrammeContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LEBLANC POST-LOSS PROGRAMME CONTINUITY
--
-- Separates survival of the NASA FSP/FICS programme from transfer of Joshua
-- LeBlanc's exact SNP I&C TechMat application carrier.
------------------------------------------------------------------------

record ProgrammeContinuityReceipt : Set where
  constructor programme-continuity-receipt
  field
    programme : String
    subject : String
    eventDate : String
    continuationReference : String
    programmeContinued : Bool
    programmeContinuedIsTrue : programmeContinued ≡ true
    namedSameRoleSuccessorLocated : Bool
    namedSameRoleSuccessorLocatedIsFalse : namedSameRoleSuccessorLocated ≡ false
    exactQualificationCarrierTransferLocated : Bool
    exactQualificationCarrierTransferLocatedIsFalse : exactQualificationCarrierTransferLocated ≡ false
    boundedReading : String

leblancFICSContinuity : ProgrammeContinuityReceipt
leblancFICSContinuity = programme-continuity-receipt
  "NASA Fission Surface Power / Fission Instrumentation & Controls for Space"
  "Joshua Kyle LeBlanc"
  "2025-07-22"
  "NASA NTRS 20250008475; FSP Technology Maturation Webinar 2025-08-26; NASA TechPort FSP active-project record updated 2026-07-15"
  true refl
  false refl
  false refl
  "FSP/FICS clearly continued after LeBlanc's death. The August 2025 webinar was presented by Robert Okojie and the wider project remained active. No same-role successor or transfer of LeBlanc's exact qualification/failure-history carrier is established here."

record LeBlancContinuityBoundary : Set where
  constructor leblanc-continuity-boundary
  field
    programmeContinuationImpliesSameCarrierTransfer : Bool
    programmeContinuationImpliesSameCarrierTransferIsFalse :
      programmeContinuationImpliesSameCarrierTransfer ≡ false
    postDeathDocumentListingImpliesPostDeathRole : Bool
    postDeathDocumentListingImpliesPostDeathRoleIsFalse :
      postDeathDocumentListingImpliesPostDeathRole ≡ false
    alternatePresenterImpliesNamedSuccessor : Bool
    alternatePresenterImpliesNamedSuccessorIsFalse :
      alternatePresenterImpliesNamedSuccessor ≡ false
    continuedProgrammeCanPressureTotalCapabilityLoss : Bool
    continuedProgrammeCanPressureTotalCapabilityLossIsTrue :
      continuedProgrammeCanPressureTotalCapabilityLoss ≡ true

canonicalLeBlancContinuityBoundary : LeBlancContinuityBoundary
canonicalLeBlancContinuityBoundary = leblanc-continuity-boundary
  false refl
  false refl
  false refl
  true refl

data LeBlancContinuityReverseTarget : Set where
  acquireNamedTechMatSuccessor : LeBlancContinuityReverseTarget
  acquireQualificationArchiveTransfer : LeBlancContinuityReverseTarget
  acquireFailureHistoryTransfer : LeBlancContinuityReverseTarget
  acquireCalibrationTransfer : LeBlancContinuityReverseTarget
  acquireRequalificationOrRebuildEvidence : LeBlancContinuityReverseTarget
  acquireMilestoneDelayEvidence : LeBlancContinuityReverseTarget
