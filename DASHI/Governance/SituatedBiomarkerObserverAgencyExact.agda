module DASHI.Governance.SituatedBiomarkerObserverAgencyExact where

-- DASHI original purpose-indexed refusal/admission boundary.
-- Reuses prior source owners without editing them:
-- Alice Brown's source-fibred educational loom (student/parent observer
-- distinction); John Anthony Brown's consent, developmental autonomy and
-- mixed-methods design; PNF EventAlgebra's candidate/admissible stages;
-- PNF numeric ABI's explicitly uninhabited authority surface.
-- The Brown authors are NOT authors of this biomarker model. Neither
-- consent nor legal authority is inferred from a person's demographic label.
-- Refusal does not imply that harm did not happen, nor does it annul
-- independently justified and lawful public-protection duties.
open import DASHI.Core.Prelude
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as John
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Interop.PNFSpectralNumericABICore as ABI

data ObserverRole : Set where
  embodiedSubject caregiver educationalInstitution
  professionalResearcher legalDecisionMaker : ObserverRole

data EvidencePurpose : Set where
  optionalBiomarkerProfiling personalResearchUse
  testimonialAccount independentlyAuthorisedLegalProcess : EvidencePurpose

data AgencyDecision : Set where
  authorises refuses notAsked : AgencyDecision

-- An optional secondary biometric use is permitted only by the subject's
-- explicit scoped authorisation. Other lawful processes are a different
-- admission question, not an exception silently manufactured by this type.
data OptionalBiomarkerPermission : AgencyDecision → Set where
  subjectAuthorises : OptionalBiomarkerPermission authorises

refusalBlocksOptionalBiomarkerUse :
  OptionalBiomarkerPermission refuses → ⊥
refusalBlocksOptionalBiomarkerUse ()

absenceOfRequestBlocksOptionalBiomarkerUse :
  OptionalBiomarkerPermission notAsked → ⊥
absenceOfRequestBlocksOptionalBiomarkerUse ()

-- The authorisation must be scoped to subject, collection and purpose.
-- It does not itself establish assay validity or legal authority.
-- Verification ownership is external; the model has no default verifier
-- and a string or a user-interface toggle is not a consent receipt.
record ConsentVerification (Subject : Set) : Set₁ where
  field
    OriginalConsent : Subject → EvidencePurpose → Set
    CurrentAuthorization : Subject → EvidencePurpose → Set
    IndependentPurposeReview : Subject → EvidencePurpose → Set

open ConsentVerification public

record ScopedBiomarkerUse
  (Subject : Set)
  (verification : ConsentVerification Subject)
  (person : Subject) : Set where
  constructor scoped-biomarker-use
  field
    choice : AgencyDecision
    purpose : EvidencePurpose
    optionalPurpose : purpose ≡ optionalBiomarkerProfiling
    subjectPermission : OptionalBiomarkerPermission choice
    originalConsentProvenance : String
    withdrawalAndRetentionRules : String
    sourceVerifiedConsent :
      OriginalConsent verification person optionalBiomarkerProfiling
    currentlyUnwithdrawn :
      CurrentAuthorization verification person optionalBiomarkerProfiling
    purposeReviewed :
      IndependentPurposeReview verification person optionalBiomarkerProfiling
    clinicalAuthorityPromoted : Bool
    clinicalAuthorityStillNotGranted :
      samplingAndClinicalAuthoritySeparatelyReviewed ≡ false

open ScopedBiomarkerUse public

-- This deliberately does not assert a universal veto over court procedure;
-- it proves only refusal of the selected optional biometric pathway.
refusedCannotProduceOptionalAdmission :
  ∀ {Subject : Set} {verification : ConsentVerification Subject}
    {person : Subject} →
  (receipt : ScopedBiomarkerUse Subject verification person) →
  choice receipt ≡ refuses → ⊥
refusedCannotProduceOptionalAdmission receipt refl =
  refusalBlocksOptionalBiomarkerUse (subjectPermission receipt)

-- Existing PNF candidate validity is NOT the same as promotion authority.
-- Note: PNF.validity=admissible can be supplied by an upstream candidate;
-- no candidate is instantiated here from a consent flag.
candidateStageNotNumericPromotion :
  ABI.PNFSpectralNumericABIPromotion → ⊥
candidateStageNotNumericPromotion =
  ABI.pnfSpectralNumericABIPromotionImpossible

-- Original Brown sources anchor provenance and observer plurality.
aliceLoomStillCandidateOnly :
  Alice.corpusLoomCandidateOnly Alice.canonicalAliceBrownCorpusLoom
    ≡ true
aliceLoomStillCandidateOnly =
  Alice.corpusLoomCandidateOnlyIsTrue Alice.canonicalAliceBrownCorpusLoom

johnMixedMethodNotForcedSingleNarrative :
  John.MixedMethodsIntegrationReceipt.forcedSingleNarrative John.canonicalMixedMethodsIntegration
    ≡ false
johnMixedMethodNotForcedSingleNarrative = refl

-- A withheld optional biomarker is not a negative observation about
-- the subject's health, agency, testimony or historical injury.
data SubjectHarm : Set where
  harmReported noHarmReported : SubjectHarm

data OptionalAccessState : Set where
  biomarkerDeclined : OptionalAccessState

access : SubjectHarm → OptionalAccessState
access _ = biomarkerDeclined

harmStatus : SubjectHarm → Bool
harmStatus harmReported = true
harmStatus noHarmReported = false

sameRefusalDoesNotIdentifyHarm :
  (access harmReported ≡ access noHarmReported)
  × (harmStatus harmReported ≡ harmStatus noHarmReported → ⊥)
sameRefusalDoesNotIdentifyHarm = refl , (λ ())
