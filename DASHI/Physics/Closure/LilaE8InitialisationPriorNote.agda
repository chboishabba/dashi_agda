module DASHI.Physics.Closure.LilaE8InitialisationPriorNote where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- LILA-E8 related-project note.
--
-- This is a provenance and claim-governance note only.  It records that
-- SPUTNIKAI/sovereign-lila-e8 is a related engineering application of E8
-- geometry as an attention/initialisation prior.  It also records that
-- AllenAI/Lila is an unrelated mathematical-reasoning benchmark, so it must
-- not be used as a provenance source for LILA-E8 or DASHI W8 origin receipts.
--
-- The note does not cite LILA-E8 benchmark results as DASHI evidence, does not
-- define an E8 carrier, and does not construct any empirical, physics, or
-- moonshine theorem.

data LilaE8RelatedProjectNoteStatus : Set where
  relatedEngineeringPriorRecordedNoDASHIClaim :
    LilaE8RelatedProjectNoteStatus

data LilaE8RelatedProjectSource : Set where
  sputnikaiSovereignLilaE8GitHub :
    LilaE8RelatedProjectSource
  sovereignLilaE8ZenodoRecord18731736 :
    LilaE8RelatedProjectSource
  bootstraptorDevCommunityPost :
    LilaE8RelatedProjectSource
  allenaiLilaBenchmarkRejectedAsUnrelated :
    LilaE8RelatedProjectSource

canonicalLilaE8RelatedProjectSources :
  List LilaE8RelatedProjectSource
canonicalLilaE8RelatedProjectSources =
  sputnikaiSovereignLilaE8GitHub
  ∷ sovereignLilaE8ZenodoRecord18731736
  ∷ bootstraptorDevCommunityPost
  ∷ allenaiLilaBenchmarkRejectedAsUnrelated
  ∷ []

data LilaE8RelatedProjectRelevance : Set where
  e8AttentionOrInitialisationPriorAnalogy :
    LilaE8RelatedProjectRelevance
  geometricPriorAnalogyWithDASHITritCarrier :
    LilaE8RelatedProjectRelevance
  leechKernelAnalogyWithMoonshineChannel :
    LilaE8RelatedProjectRelevance
  engineeringSourceOnly :
    LilaE8RelatedProjectRelevance

canonicalLilaE8RelatedProjectRelevance :
  List LilaE8RelatedProjectRelevance
canonicalLilaE8RelatedProjectRelevance =
  e8AttentionOrInitialisationPriorAnalogy
  ∷ geometricPriorAnalogyWithDASHITritCarrier
  ∷ leechKernelAnalogyWithMoonshineChannel
  ∷ engineeringSourceOnly
  ∷ []

data LilaE8RejectedProvenanceOrClaim : Set where
  rejectAllenAIAttribution :
    LilaE8RejectedProvenanceOrClaim
  rejectTinyStoriesAsDASHIPhysicsEvidence :
    LilaE8RejectedProvenanceOrClaim
  rejectGeometricResonanceAsDASHITypedTerm :
    LilaE8RejectedProvenanceOrClaim
  rejectZeroViscosityAsDASHITypedTerm :
    LilaE8RejectedProvenanceOrClaim
  rejectMoonshineMarketingAsMoonshineProof :
    LilaE8RejectedProvenanceOrClaim

canonicalLilaE8RejectedProvenanceOrClaims :
  List LilaE8RejectedProvenanceOrClaim
canonicalLilaE8RejectedProvenanceOrClaims =
  rejectAllenAIAttribution
  ∷ rejectTinyStoriesAsDASHIPhysicsEvidence
  ∷ rejectGeometricResonanceAsDASHITypedTerm
  ∷ rejectZeroViscosityAsDASHITypedTerm
  ∷ rejectMoonshineMarketingAsMoonshineProof
  ∷ []

data LilaE8RelatedProjectBoundary : Set where
  noteOnlyNotTheorem :
    LilaE8RelatedProjectBoundary
  noDASHIEmpiricalClaim :
    LilaE8RelatedProjectBoundary
  noDASHIPhysicsPromotion :
    LilaE8RelatedProjectBoundary
  noW8OriginReceiptPromotion :
    LilaE8RelatedProjectBoundary
  noAcceptedE8Carrier :
    LilaE8RelatedProjectBoundary

canonicalLilaE8RelatedProjectBoundaries :
  List LilaE8RelatedProjectBoundary
canonicalLilaE8RelatedProjectBoundaries =
  noteOnlyNotTheorem
  ∷ noDASHIEmpiricalClaim
  ∷ noDASHIPhysicsPromotion
  ∷ noW8OriginReceiptPromotion
  ∷ noAcceptedE8Carrier
  ∷ []

data DASHIReceiptPromotedByLilaE8RelatedProjectNote : Set where

lilaE8RelatedProjectNotePromotionImpossibleHere :
  DASHIReceiptPromotedByLilaE8RelatedProjectNote →
  ⊥
lilaE8RelatedProjectNotePromotionImpossibleHere ()

record LilaE8RelatedProjectNote : Setω where
  field
    status :
      LilaE8RelatedProjectNoteStatus

    projectRepo :
      String

    projectRepoIsCanonical :
      projectRepo ≡ "https://github.com/SPUTNIKAI/sovereign-lila-e8"

    zenodoRecord :
      String

    zenodoRecordIsCanonical :
      zenodoRecord ≡ "https://zenodo.org/records/18731736"

    rejectedAllenAIRepo :
      String

    rejectedAllenAIRepoIsCanonical :
      rejectedAllenAIRepo ≡ "https://github.com/allenai/lila"

    allenAILilaIsUnrelated :
      Bool

    allenAILilaIsUnrelatedIsTrue :
      allenAILilaIsUnrelated ≡ true

    sources :
      List LilaE8RelatedProjectSource

    sourcesAreCanonical :
      sources ≡ canonicalLilaE8RelatedProjectSources

    relevance :
      List LilaE8RelatedProjectRelevance

    relevanceIsCanonical :
      relevance ≡ canonicalLilaE8RelatedProjectRelevance

    rejectedClaims :
      List LilaE8RejectedProvenanceOrClaim

    rejectedClaimsAreCanonical :
      rejectedClaims ≡ canonicalLilaE8RejectedProvenanceOrClaims

    noteOnly :
      Bool

    noteOnlyIsTrue :
      noteOnly ≡ true

    acceptedDASHIEvidence :
      Bool

    acceptedDASHIEvidenceIsFalse :
      acceptedDASHIEvidence ≡ false

    boundary :
      List LilaE8RelatedProjectBoundary

    boundaryIsCanonical :
      boundary ≡ canonicalLilaE8RelatedProjectBoundaries

    futurePromotionBlocked :
      DASHIReceiptPromotedByLilaE8RelatedProjectNote →
      ⊥

canonicalLilaE8RelatedProjectNote :
  LilaE8RelatedProjectNote
canonicalLilaE8RelatedProjectNote =
  record
    { status =
        relatedEngineeringPriorRecordedNoDASHIClaim
    ; projectRepo =
        "https://github.com/SPUTNIKAI/sovereign-lila-e8"
    ; projectRepoIsCanonical =
        refl
    ; zenodoRecord =
        "https://zenodo.org/records/18731736"
    ; zenodoRecordIsCanonical =
        refl
    ; rejectedAllenAIRepo =
        "https://github.com/allenai/lila"
    ; rejectedAllenAIRepoIsCanonical =
        refl
    ; allenAILilaIsUnrelated =
        true
    ; allenAILilaIsUnrelatedIsTrue =
        refl
    ; sources =
        canonicalLilaE8RelatedProjectSources
    ; sourcesAreCanonical =
        refl
    ; relevance =
        canonicalLilaE8RelatedProjectRelevance
    ; relevanceIsCanonical =
        refl
    ; rejectedClaims =
        canonicalLilaE8RejectedProvenanceOrClaims
    ; rejectedClaimsAreCanonical =
        refl
    ; noteOnly =
        true
    ; noteOnlyIsTrue =
        refl
    ; acceptedDASHIEvidence =
        false
    ; acceptedDASHIEvidenceIsFalse =
        refl
    ; boundary =
        canonicalLilaE8RelatedProjectBoundaries
    ; boundaryIsCanonical =
        refl
    ; futurePromotionBlocked =
        lilaE8RelatedProjectNotePromotionImpossibleHere
    }

canonicalLilaE8RelatedProjectNoteStatus :
  LilaE8RelatedProjectNoteStatus
canonicalLilaE8RelatedProjectNoteStatus =
  LilaE8RelatedProjectNote.status canonicalLilaE8RelatedProjectNote
