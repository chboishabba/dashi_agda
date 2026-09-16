module DASHI.Reasoning.ContentAddressedVerificationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Interop.SensibLawFederatedZOSAcquisitionExact as Federated
import DASHI.Interop.WikimediaWorldBucketPublicationExact as WorldBucket
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM

------------------------------------------------------------------------
-- CONTENT-ADDRESSED VERIFICATION BRIDGE
--
-- JMD's supplied RequestProject/RepublicVerification.lean proves, in Lean,
-- that a verdict depending only on content factors through content, and that an
-- injective CID can serve as a faithful address for such a verdict.  DASHI
-- retains that formal-source result while keeping three surfaces distinct:
--
--   content identity / address
--   procedural invariance of a verifier
--   epistemic correctness of the verifier
--
-- A CID or a content-addressed procedure can establish the first two without
-- manufacturing the third.
------------------------------------------------------------------------

record LeanContentAddressedSourceContract : Set where
  constructor leanContentAddressedSourceContract
  field
    sourceModule : String
    contentAddressedDefinition : String
    reputationAddressedDefinition : String
    factoringTheorem : String
    cidForwardTheorem : String
    cidReverseTheorem : String
    demandTheorem : String
    sourceOwner : String
    sourceHash : String

open LeanContentAddressedSourceContract public

jmdRepublicVerificationContract : LeanContentAddressedSourceContract
jmdRepublicVerificationContract =
  leanContentAddressedSourceContract
    "RequestProject.RepublicVerification"
    "Plato.Republic.Verification.ContentAddressed"
    "Plato.Republic.Verification.ReputationAddressed"
    "Plato.Republic.Verification.content_addressed_iff_factors"
    "Plato.Republic.Verification.cid_factoring_is_content_addressed"
    "Plato.Republic.Verification.content_addressed_factors_through_cid"
    "Plato.Republic.Verification.demand_met_iff_content_addressed"
    "James Michael DuPont (JMD / meta-introspector)"
    Source.archiveSha256

record ContentAddressedVerificationBoundary : Set where
  constructor contentAddressedVerificationBoundary
  field
    sameContentRequiresSameVerdict : Bool
    contentFactoringRepresentsProceduralInvariance : Bool
    injectiveCIDMayAddressContent : Bool
    cidCreatesSemanticAuthority : Bool
    contentAddressingCreatesClaimTruth : Bool
    contentAddressingCreatesEvidencePayment : Bool
    verifierCorrectnessMustBePaidSeparately : Bool
    sourceOwnershipRetained : Bool
    sourceTheoremImportedAsAgdaProof : Bool

open ContentAddressedVerificationBoundary public

canonicalContentAddressedVerificationBoundary : ContentAddressedVerificationBoundary
canonicalContentAddressedVerificationBoundary =
  contentAddressedVerificationBoundary
    true
    true
    true
    false
    false
    false
    true
    true
    false

------------------------------------------------------------------------
-- Finite collision: two verifiers are equally content-addressed at the
-- procedural surface but differ in epistemic correctness.  Therefore
-- correctness cannot factor through "is content-addressed" alone.
------------------------------------------------------------------------

data VerificationWorld : Set where
  contentAddressedCorrectVerifier : VerificationWorld
  contentAddressedWrongVerifier : VerificationWorld

data ContentAddressedSurface : Set where
  sameContentAddressedProcedure : ContentAddressedSurface

data VerificationQuery : Set where
  correctnessQuestion : VerificationQuery

data VerificationAnswer : Set where
  verifierCorrectHere : VerificationAnswer
  verifierWrongHere : VerificationAnswer

contentAddressingSurface : VerificationWorld → ContentAddressedSurface
contentAddressingSurface contentAddressedCorrectVerifier = sameContentAddressedProcedure
contentAddressingSurface contentAddressedWrongVerifier = sameContentAddressedProcedure

VerificationAnswerFor : VerificationQuery → Set
VerificationAnswerFor correctnessQuestion = VerificationAnswer

askVerification :
  (query : VerificationQuery) →
  VerificationWorld →
  VerificationAnswerFor query
askVerification correctnessQuestion contentAddressedCorrectVerifier = verifierCorrectHere
askVerification correctnessQuestion contentAddressedWrongVerifier = verifierWrongHere

verificationQuestions : Query.InquiryQuestionFamily VerificationWorld VerificationQuery
verificationQuestions = Query.inquiryQuestionFamily VerificationAnswerFor askVerification

contentAddressingDoesNotDetermineCorrectness :
  Query.FactorsThrough
    verificationQuestions
    contentAddressingSurface
    correctnessQuestion →
  ⊥
contentAddressingDoesNotDetermineCorrectness factor = helper first second
  where
    first :
      verifierCorrectHere ≡ Query.quotientAnswer factor sameContentAddressedProcedure
    first = Query.factorisation factor contentAddressedCorrectVerifier

    second :
      verifierWrongHere ≡ Query.quotientAnswer factor sameContentAddressedProcedure
    second = Query.factorisation factor contentAddressedWrongVerifier

    helper :
      verifierCorrectHere ≡ Query.quotientAnswer factor sameContentAddressedProcedure →
      verifierWrongHere ≡ Query.quotientAnswer factor sameContentAddressedProcedure →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Explicit authority firewalls.
------------------------------------------------------------------------

data ContentAddressingCreatesTruth : Set where
data CIDCreatesSemanticAuthority : Set where
data CIDImportsProof : Set where
data MirrorAvailabilityPaysEvidence : Set where

contentAddressingDoesNotCreateTruth : ContentAddressingCreatesTruth → ⊥
contentAddressingDoesNotCreateTruth ()

cidDoesNotCreateSemanticAuthority : CIDCreatesSemanticAuthority → ⊥
cidDoesNotCreateSemanticAuthority ()

cidDoesNotImportProof : CIDImportsProof → ⊥
cidDoesNotImportProof ()

mirrorAvailabilityDoesNotPayEvidence : MirrorAvailabilityPaysEvidence → ⊥
mirrorAvailabilityDoesNotPayEvidence ()

------------------------------------------------------------------------
-- Existing publication/presentation owners are imported rather than cloned.
------------------------------------------------------------------------

existingFederatedContentBoundary : Federated.FederatedContentBoundary
existingFederatedContentBoundary = Federated.canonicalFederatedContentBoundary

existingWorldBucketManifestBoundary : WorldBucket.WorldBucketManifestBoundary
existingWorldBucketManifestBoundary = WorldBucket.canonicalManifestBoundary

existingSFMViewAuthorityBoundary : SFM.SFMViewAuthorityBoundary
existingSFMViewAuthorityBoundary = SFM.canonicalSFMViewAuthorityBoundary

contentAddressingIsProceduralNotEpistemic : String
contentAddressingIsProceduralNotEpistemic =
  "content-addressed verdicts preserve same-content procedural invariance; claim truth, source support, semantic authority and evidence payment remain separate obligations"
