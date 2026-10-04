module DASHI.Cognition.PNF.SensibLawProviderLegalSourceRegistrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCProviderPinnedEphemeralMaterialisationExact as Provider

------------------------------------------------------------------------
-- Port of the historical SensibLaw source-admission/legal-source-revision
-- boundary to the provider-materialised runtime.
--
-- The registration says that an exactly identified provider source is eligible
-- to enter the legal compiler/source-selection layer. It does not review a
-- proposition, choose evidence role or normative order, establish applicability,
-- or create legal authority/truth.
------------------------------------------------------------------------

record ProviderLegalSourceRegistration : Set where
  constructor provider-legal-source-registration
  field
    materialisationRef : String
    sourceRevisionRef : String
    documentRef : String
    admissionReceiptRef : String
    providerAcquisitionReceiptRef : String
    jurisdictionRef : String
    sourceRoleRef : String
    authorityLevelRef : String
    semanticScopeRef : String
    canonicalDigestRef : String
    compileEligible : Bool
    compileEligibleIsTrue : compileEligible ≡ true
    residentBytesRequiredForLegalSourceIdentity : Bool
    residentBytesRequiredForLegalSourceIdentityIsFalse :
      residentBytesRequiredForLegalSourceIdentity ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ProviderLegalSourceRegistration public

record ExactSlicePaymentBoundary : Set where
  constructor exact-slice-payment-boundary
  field
    providerPinMustAlreadyBeVerified : Bool
    providerPinMustAlreadyBeVerifiedIsTrue : providerPinMustAlreadyBeVerified ≡ true
    exactBytesMustBeResident : Bool
    exactBytesMustBeResidentIsTrue : exactBytesMustBeResident ≡ true
    exactSliceDigestPersisted : Bool
    exactSliceDigestPersistedIsTrue : exactSliceDigestPersisted ≡ true
    slicePaymentCreatesPropositionMeaning : Bool
    slicePaymentCreatesPropositionMeaningIsFalse : slicePaymentCreatesPropositionMeaning ≡ false
    slicePaymentChoosesEvidenceRole : Bool
    slicePaymentChoosesEvidenceRoleIsFalse : slicePaymentChoosesEvidenceRole ≡ false
    slicePaymentChoosesNormativeOrder : Bool
    slicePaymentChoosesNormativeOrderIsFalse : slicePaymentChoosesNormativeOrder ≡ false

open ExactSlicePaymentBoundary public

canonicalExactSlicePaymentBoundary : ExactSlicePaymentBoundary
canonicalExactSlicePaymentBoundary =
  exact-slice-payment-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- The provider materialisation owner remains upstream of this registration.
------------------------------------------------------------------------

_ : Set
_ = Provider.ImmutableProviderPin

_ : Set
_ = Provider.EvictionSafeSourceBoundary

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data CompileEligibleEqualsLegalAuthority : Set where
data LegalSourceRegistrationEqualsReviewedEvidence : Set where
data LegalSourceRegistrationChoosesNormativeOrder : Set where
data LegalSourceRegistrationClosesApplicability : Set where
data ExactSliceEqualsPropositionSupport : Set where
data EvictedBytesDestroyLegalSourceIdentity : Set where

compileEligibilityDoesNotCreateLegalAuthority : CompileEligibleEqualsLegalAuthority → ⊥
compileEligibilityDoesNotCreateLegalAuthority ()

registrationDoesNotEqualReviewedEvidence : LegalSourceRegistrationEqualsReviewedEvidence → ⊥
registrationDoesNotEqualReviewedEvidence ()

registrationDoesNotChooseNormativeOrder : LegalSourceRegistrationChoosesNormativeOrder → ⊥
registrationDoesNotChooseNormativeOrder ()

registrationDoesNotCloseApplicability : LegalSourceRegistrationClosesApplicability → ⊥
registrationDoesNotCloseApplicability ()

exactSliceDoesNotEqualPropositionSupport : ExactSliceEqualsPropositionSupport → ⊥
exactSliceDoesNotEqualPropositionSupport ()

evictedBytesDoNotDestroyLegalSourceIdentity : EvictedBytesDestroyLegalSourceIdentity → ⊥
evictedBytesDoNotDestroyLegalSourceIdentity ()
