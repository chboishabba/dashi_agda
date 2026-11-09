{-# OPTIONS --safe #-}
module DASHI.Cognition.CCDCOEP3StakeholderHandoffExact where

------------------------------------------------------------------------
-- Original sources/credit: 2015 Turkish G20 Presidency reports C20
-- communiqué receipt; ICC reports the B20 presentation. C20/B20 own
-- their recommendations, and G20/COP parties own adopted instruments.
-- These cases do not yield evidence of clause adoption or causality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data OriginalVoice : Set where
  civil20 : OriginalVoice
  business20 : OriginalVoice
  energyMinisters : OriginalVoice
  leaders : OriginalVoice
  conferenceOfParties : OriginalVoice

data EvidenceLevel : Set where
  publishedProposal : EvidenceLevel
  attributedPresentation : EvidenceLevel
  officialReceivedCommunication : EvidenceLevel
  adoptedPolicyText : EvidenceLevel
  provedDraftUptake : EvidenceLevel

record EvidenceItem : Set where
  constructor evidenceItem
  field
    originalVoice : OriginalVoice
    level : EvidenceLevel

c20PresidencyReceipt : EvidenceItem
c20PresidencyReceipt =
  evidenceItem civil20 officialReceivedCommunication

b20ICCPresentationAccount : EvidenceItem
b20ICCPresentationAccount =
  evidenceItem business20 attributedPresentation

ministerialAdoptedCommunique : EvidenceItem
ministerialAdoptedCommunique =
  evidenceItem energyMinisters adoptedPolicyText

-- A handoff cannot become a leaders' adopted speech act just by
-- erasing original source identity.
c20ReceiptIsNotLeadersAuthorship :
  EvidenceItem.originalVoice c20PresidencyReceipt ≡ leaders → ⊥
c20ReceiptIsNotLeadersAuthorship ()

b20PresentationNotDraftUptake :
  EvidenceItem.level b20ICCPresentationAccount ≡ provedDraftUptake → ⊥
b20PresentationNotDraftUptake ()

c20ReceiptNotPolicyAdoption :
  EvidenceItem.level c20PresidencyReceipt ≡ adoptedPolicyText → ⊥
c20ReceiptNotPolicyAdoption ()
