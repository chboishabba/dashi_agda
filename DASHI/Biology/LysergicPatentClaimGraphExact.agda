{-# OPTIONS --safe #-}
module DASHI.Biology.LysergicPatentClaimGraphExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- LIMITED, NON-OPERATIONAL CLAIM-REFERENCE AUDIT.
--
-- In Google Patents' HTML rendering of WO2015195535A2, claim 28 reads
-- as depending on claims 26, 27 and 28.  That creates a displayed
-- self-reference. This file proves only membership in the captured
-- finite list, not an error in the official filed claims, patent
-- invalidity, infringement, or a chemical method.
--
-- Inventors: Daniel G. Panaccione; Sarah L. Robinson.
-- Original assignee: West Virginia University.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ (x : Nat) : List Nat → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

htmlObservedClaimCount : Nat
htmlObservedClaimCount = 35

htmlClaim28Dependencies : List Nat
htmlClaim28Dependencies = 26 ∷ 27 ∷ 28 ∷ []

htmlClaim28SelfReference : 28 ∈ htmlClaim28Dependencies
htmlClaim28SelfReference = there (there here)

data ClaimTextEvidenceTier : Set where
  publicHtmlRendering : ClaimTextEvidenceTier
  originalFiledPublicationVerified : ClaimTextEvidenceTier

data OfficialClaimTextAdmission : ClaimTextEvidenceTier → Set where
  verifiedOriginalDocument :
    OfficialClaimTextAdmission originalFiledPublicationVerified

data NoOfficialConfirmation : Set where

htmlRenderingNotOfficialVerification :
  OfficialClaimTextAdmission publicHtmlRendering → NoOfficialConfirmation
htmlRenderingNotOfficialVerification ()

record BoundedClaimTextDiscrepancy : Set where
  constructor boundedClaimTextDiscrepancy
  field
    publication : String
    indexedSourceURL : String
    selectedClaimNumber : Nat
    referenceListAsDisplayed : List Nat
    evidenceTier : ClaimTextEvidenceTier
    provisionalReading : String

    originalClaimFileCompared : Bool
    originalClaimFileComparedIsFalse :
      originalClaimFileCompared ≡ false

    legalDefectConcluded : Bool
    legalDefectConcludedIsFalse :
      legalDefectConcluded ≡ false

htmlClaim28Discrepancy : BoundedClaimTextDiscrepancy
htmlClaim28Discrepancy =
  boundedClaimTextDiscrepancy
    "WO2015195535A2"
    "https://patents.google.com/patent/WO2015195535A2/en"
    28
    htmlClaim28Dependencies
    publicHtmlRendering
    "Indexed claim 28 lists itself among its dependencies. Inspect the official filing before deciding whether this is an original text defect or a rendering error."
    false refl
    false refl

------------------------------------------------------------------------
-- The proof is strictly about a source-rendered list of integers.
-- No claim construction, legal opinion or technical implementation.
------------------------------------------------------------------------
