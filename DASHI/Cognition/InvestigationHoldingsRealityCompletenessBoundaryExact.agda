module DASHI.Cognition.InvestigationHoldingsRealityCompletenessBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record CompletenessBoundary : Set where
  constructor completeness-boundary
  field
    exhaustiveReviewOfAgencyHoldingsClaimed : Bool
    agencyHoldingsEqualAllRelevantReality : Bool
    absenceFromReleasedFilesExoneratesGlobally : Bool
    withheldRedactedOrNonSearchableMaterialExists : Bool
    missingWitnessOrThirdPartyRecordsPossible : Bool
    completenessMustBeClaimLocal : Bool
open CompletenessBoundary public

canonicalCompletenessBoundary : CompletenessBoundary
canonicalCompletenessBoundary = completeness-boundary
  true false false true true true

record CompletenessReceipt : Set where
  constructor completeness-receipt
  field
    source : String
    boundedFinding : String
    holdingsReviewPaid : Bool
    universalRealityCompletenessPaid : Bool
open CompletenessReceipt public

dojFbi2025Receipt : CompletenessReceipt
dojFbi2025Receipt = completeness-receipt
  "DOJ/FBI July 2025 memorandum"
  "DOJ/FBI described an exhaustive review of investigative holdings, including digital and physical searches. This pays review-of-holdings, not proof that all relevant real-world evidence had ever entered those holdings."
  true false

doj2026ProductionReceipt : CompletenessReceipt
doj2026ProductionReceipt = completeness-receipt
  "DOJ January 30 2026 EFTA production letter and Epstein Library"
  "DOJ described production from Department-held responsive materials subject to identified exceptions/redactions; the public library also warns that some materials are not reliably electronically searchable."
  true false

congressionalChallengeReceipt : CompletenessReceipt
congressionalChallengeReceipt = completeness-receipt
  "House Judiciary/Oversight Democratic members, March 19 2026 letter"
  "Members alleged missing FD-302s, withheld documents and incomplete production. This pays existence of an oversight dispute, not the truth of every allegation in the letter."
  true false

data HoldingsCompletenessImpliesRealityCompleteness : Set where
data AbsenceFromReleaseImpliesNonOccurrence : Set where
data SearchFailureImpliesDocumentAbsence : Set where

holdingsDoNotEqualReality : HoldingsCompletenessImpliesRealityCompleteness → ⊥
holdingsDoNotEqualReality ()

releaseAbsenceDoesNotProveNonOccurrence : AbsenceFromReleaseImpliesNonOccurrence → ⊥
releaseAbsenceDoesNotProveNonOccurrence ()

searchFailureDoesNotProveDocumentAbsence : SearchFailureImpliesDocumentAbsence → ⊥
searchFailureDoesNotProveDocumentAbsence ()
