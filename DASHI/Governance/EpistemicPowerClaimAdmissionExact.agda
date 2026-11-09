module DASHI.Governance.EpistemicPowerClaimAdmissionExact where

-- Claims require their own evidence: bibliography != source interpretation,
-- source interpretation != human observation, observation != causal conclusion,
-- formal model != political authority. This is a source/claim admission logic,
-- not a validation of any particular real-world case.
open import DASHI.Core.Prelude

data ClaimKind : Set where
  textualClaim fatigueClaim causalClaim landClaim sovereigntyClaim : ClaimKind

data ReceiptKind : Set where
  locatedPassage independentObservation causalComparison
  landSpecificEvidence sovereigntySpecificEvidence : ReceiptKind

data Supports : ReceiptKind → ClaimKind → Set where
  passagePaysText : Supports locatedPassage textualClaim
  observationPaysFatigue : Supports independentObservation fatigueClaim
  comparisonPaysCause : Supports causalComparison causalClaim
  landPaysLand : Supports landSpecificEvidence landClaim
  sovereigntyPaysSovereignty : Supports sovereigntySpecificEvidence sovereigntyClaim

record Admission (claim : ClaimKind) : Set where
  constructor admit
  field
    receipt : ReceiptKind
    supports : Supports receipt claim

open Admission public

textAdmission : Admission textualClaim
textAdmission = admit locatedPassage passagePaysText

fatigueAdmission : Admission fatigueClaim
fatigueAdmission = admit independentObservation observationPaysFatigue

causalAdmission : Admission causalClaim
causalAdmission = admit causalComparison comparisonPaysCause

landAdmission : Admission landClaim
landAdmission = admit landSpecificEvidence landPaysLand

sovereigntyAdmission : Admission sovereigntyClaim
sovereigntyAdmission = admit sovereigntySpecificEvidence sovereigntyPaysSovereignty

sourceLocationDoesNotAdmitFatigue :
  Supports locatedPassage fatigueClaim → ⊥
sourceLocationDoesNotAdmitFatigue ()

sourceLocationDoesNotAdmitCausation :
  Supports locatedPassage causalClaim → ⊥
sourceLocationDoesNotAdmitCausation ()

fatigueObservationDoesNotAdmitCausation :
  Supports independentObservation causalClaim → ⊥
fatigueObservationDoesNotAdmitCausation ()

landReceiptDoesNotAdmitSovereignty :
  Supports landSpecificEvidence sovereigntyClaim → ⊥
landReceiptDoesNotAdmitSovereignty ()

sovereigntyReceiptDoesNotAdmitLand :
  Supports sovereigntySpecificEvidence landClaim → ⊥
sovereigntyReceiptDoesNotAdmitLand ()

inclusionOrTextCannotAdmitLand :
  Supports locatedPassage landClaim → ⊥
inclusionOrTextCannotAdmitLand ()

record RequiredCaseBundle : Set where
  constructor required-case-bundle
  field
    originalText : Admission textualClaim
    observedFatigue : Admission fatigueClaim
    matchedCause : Admission causalClaim
    landEvidence : Admission landClaim
    sovereigntyEvidence : Admission sovereigntyClaim

bundleDoesNotConflateReceipts :
  RequiredCaseBundle
bundleDoesNotConflateReceipts =
  required-case-bundle
    textAdmission fatigueAdmission causalAdmission
    landAdmission sovereigntyAdmission

-- Importantly: constructors here encode *types of required evidence*.
-- The synthetic bundle is not a receipt that such evidence exists.
