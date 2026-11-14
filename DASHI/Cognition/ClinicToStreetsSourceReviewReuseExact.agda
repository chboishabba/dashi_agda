module DASHI.Cognition.ClinicToStreetsSourceReviewReuseExact where

------------------------------------------------------------------------
-- CLINIC-TO-STREETS SOURCE + REVIEW REUSE
--
-- This owner pays two previously loose boundaries without introducing another
-- source or review ontology:
--
--   1. publisher/book metadata is represented with AttributedSourceCore;
--   2. any future human review uses the domain-neutral HumanReviewCore exact
--      review receipt and item-provenance binding.
--
-- The supplied reel transcript remains the immediate source for the two
-- transcript-facing claims in ClinicToStreetsCausalProvenanceExact. The book
-- citation records the attributed upstream work; it does not prove that the
-- transcript paraphrase is textually exact, that the theoretical claim is true,
-- or that any empirical causal edge is identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.HumanReviewCore as Review
import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as Clinic

------------------------------------------------------------------------
-- 1. Primary publisher metadata on the canonical attributed-source carrier.
------------------------------------------------------------------------

clinicBookSource : Source.AttributedSource
clinicBookSource =
  Source.mkNoDOISource
    "Lara Sheehi"
    "From the Clinic to the Streets: Psychoanalysis for Revolutionary Futures"
    "Pluto Press; paperback ISBN 9780745350059; ebook ISBN 9780745350066"
    "2026"
    "https://www.plutobooks.com/product/from-the-clinic-to-the-streets/"
    Source.academicBookSource
    "publisher metadata and upstream theoretical source attributed by the supplied reel; citation does not import theorem truth, textual identity with the reel paraphrase, clinical authority, political authority, or empirical causal identification"
    Source.publicAttribution

clinicSourceAtlas : Source.AttributedSourceAtlas
clinicSourceAtlas =
  Source.mkSourceAtlas
    "Clinic-to-Streets attributed-source boundary"
    "DASHI.Cognition.ClinicToStreetsSourceReviewReuseExact"
    (clinicBookSource ∷ [])
    "bounded source atlas for the Clinic-to-Streets formalisation; the supplied reel transcript remains a separate conversation source and is not silently identified with the book text"

bookCitationDoesNotImportProof :
  Source.citationImportsProof clinicBookSource ≡ false
bookCitationDoesNotImportProof =
  Source.citationImportsProofIsFalse clinicBookSource

bookCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority clinicBookSource ≡ false
bookCitationDoesNotCreateAuthority =
  Source.citationCreatesAuthorityIsFalse clinicBookSource

sourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority clinicSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority =
  Source.atlasCreatesAuthorityIsFalse clinicSourceAtlas

------------------------------------------------------------------------
-- 2. Exact transcript-facing claim identities.
------------------------------------------------------------------------

data ClinicClaimId : Set where
  familyActivationClaimId : ClinicClaimId
  therapyCounterinsurgencyClaimId : ClinicClaimId

claimById : ClinicClaimId → Clinic.SourceClaim
claimById familyActivationClaimId = Clinic.familyActivationClaim
claimById therapyCounterinsurgencyClaimId = Clinic.therapyCounterinsurgencyClaim

claimReference : ClinicClaimId → String
claimReference familyActivationClaimId =
  "clinic-reel-2026-10-05#135-145-family-activation"
claimReference therapyCounterinsurgencyClaimId =
  "clinic-reel-2026-10-05#29-38-therapy-counterinsurgency"

------------------------------------------------------------------------
-- 3. Review demand over HumanReviewCore.
--
-- We deliberately do not fabricate a GenericHumanReviewReceipt. Current
-- demands are unpaid. A future reviewed claim must bind the exact source
-- manifestation, candidate claim, and declared consumer and must carry an
-- accepted/qualified exact-item binding.
------------------------------------------------------------------------

record ClinicReviewDemand (id : ClinicClaimId) : Set where
  constructor clinic-review-demand
  field
    sourceManifestationReference : String
    candidateClaimReference : String
    consumerReference : String
    reviewPaid : Bool
    reviewCreatesClaimTruth : Bool
    reviewCreatesCausalIdentification : Bool

open ClinicReviewDemand public

familyActivationReviewDemand :
  ClinicReviewDemand familyActivationClaimId
familyActivationReviewDemand =
  clinic-review-demand
    "supplied transcript-2026-10-05.srt / exact durable repository manifestation still to be pinned"
    (claimReference familyActivationClaimId)
    "family/intimate activation interpretation consumer"
    false
    false
    false

therapyCounterinsurgencyReviewDemand :
  ClinicReviewDemand therapyCounterinsurgencyClaimId
therapyCounterinsurgencyReviewDemand =
  clinic-review-demand
    "supplied transcript-2026-10-05.srt / exact durable repository manifestation still to be pinned"
    (claimReference therapyCounterinsurgencyClaimId)
    "therapy/counterinsurgent-effect interpretation consumer"
    false
    false
    false

record ReviewedClinicClaim
    (id : ClinicClaimId)
    (demand : ClinicReviewDemand id) : Set where
  constructor reviewed-clinic-claim
  field
    demandIsPaid : reviewPaid demand ≡ true
    genericReview : Review.GenericHumanReviewReceipt
    exactReviewItemBinding : Review.ExactReviewItemBinding

    reviewItemMatchesClaim :
      Review.reviewItemRef genericReview
      ≡ candidateClaimReference demand

    sourceBindingMatchesDemand :
      Review.sourceManifestationRef exactReviewItemBinding
      ≡ sourceManifestationReference demand

    candidateBindingMatchesClaim :
      Review.candidateFactorRef exactReviewItemBinding
      ≡ candidateClaimReference demand

    consumerBindingMatchesDemand :
      Review.consumerRef exactReviewItemBinding
      ≡ consumerReference demand

    claimTruthStillNotPromoted :
      reviewCreatesClaimTruth demand ≡ false

    causalIdentificationStillNotPromoted :
      reviewCreatesCausalIdentification demand ≡ false

open ReviewedClinicClaim public

familyActivationReviewCurrentlyUnpaid :
  reviewPaid familyActivationReviewDemand ≡ false
familyActivationReviewCurrentlyUnpaid = refl

therapyCounterinsurgencyReviewCurrentlyUnpaid :
  reviewPaid therapyCounterinsurgencyReviewDemand ≡ false
therapyCounterinsurgencyReviewCurrentlyUnpaid = refl

familyActivationCurrentCannotSupplyReviewedClaim :
  ReviewedClinicClaim
    familyActivationClaimId
    familyActivationReviewDemand →
  ⊥
familyActivationCurrentCannotSupplyReviewedClaim reviewed
  with demandIsPaid reviewed
... | ()

therapyCounterinsurgencyCurrentCannotSupplyReviewedClaim :
  ReviewedClinicClaim
    therapyCounterinsurgencyClaimId
    therapyCounterinsurgencyReviewDemand →
  ⊥
therapyCounterinsurgencyCurrentCannotSupplyReviewedClaim reviewed
  with demandIsPaid reviewed
... | ()

------------------------------------------------------------------------
-- 4. Non-substitution firewalls.
------------------------------------------------------------------------

data ReviewPaymentImpliesClaimTruth : Set where
data ReviewPaymentImpliesCausalIdentification : Set where
data BookCitationImpliesReelTextualIdentity : Set where
data PublisherMetadataImpliesTheoryTruth : Set where

reviewPaymentDoesNotEstablishClaimTruth :
  ReviewPaymentImpliesClaimTruth → ⊥
reviewPaymentDoesNotEstablishClaimTruth ()

reviewPaymentDoesNotEstablishCausalIdentification :
  ReviewPaymentImpliesCausalIdentification → ⊥
reviewPaymentDoesNotEstablishCausalIdentification ()

bookCitationDoesNotEstablishReelTextualIdentity :
  BookCitationImpliesReelTextualIdentity → ⊥
bookCitationDoesNotEstablishReelTextualIdentity ()

publisherMetadataDoesNotEstablishTheoryTruth :
  PublisherMetadataImpliesTheoryTruth → ⊥
publisherMetadataDoesNotEstablishTheoryTruth ()

------------------------------------------------------------------------
-- 5. Boundary receipt.
------------------------------------------------------------------------

record ClinicSourceReviewBoundary : Set where
  constructor clinic-source-review-boundary
  field
    attributedSourceCoreReused : Bool
    humanReviewCoreReused : Bool
    exactReviewItemBindingRequired : Bool
    currentFamilyActivationReviewPaid : Bool
    currentTherapyCounterinsurgencyReviewPaid : Bool
    bookCitationImportsProof : Bool
    reviewPromotesClaimTruth : Bool
    reviewPromotesCausalIdentification : Bool
    reelParaphraseIdentifiedWithBookText : Bool

canonicalClinicSourceReviewBoundary : ClinicSourceReviewBoundary
canonicalClinicSourceReviewBoundary =
  clinic-source-review-boundary
    true true true false false false false false false
