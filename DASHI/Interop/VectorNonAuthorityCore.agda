module DASHI.Interop.VectorNonAuthorityCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable vector non-authority core.
--
-- This module factors the common object vocabulary for vector, spectral,
-- proximity, ranking, and arithmetic proposal lanes.  A value in this core is
-- candidate evidence only.  It can describe a hit, a score, a rank, or an
-- arithmetic/vector transport proposal, but it cannot by itself carry truth,
-- committed support, admissibility, or trading authority.

data VectorNonAuthorityCoreStatus : Set where
  vectorNonAuthorityCore_candidateOnly :
    VectorNonAuthorityCoreStatus

data ⊤-local : Set where
  tt-local : ⊤-local

data ObjectRef : Set where
  objectRef :
    Nat →
    String →
    ObjectRef

data CandidateRef : Set where
  candidateRef :
    Nat →
    String →
    CandidateRef

data EvidenceRef : Set where
  evidenceRef :
    Nat →
    String →
    EvidenceRef

data IndexRef : Set where
  indexRef :
    Nat →
    String →
    IndexRef

data VectorCoordinate : Set where
  vectorCoordinate :
    Nat →
    String →
    VectorCoordinate

data ScoreRef : Set where
  scoreRef :
    Nat →
    String →
    ScoreRef

data RankRef : Set where
  rankRef :
    Nat →
    String →
    RankRef

fallbackObjectRef : ObjectRef
fallbackObjectRef =
  objectRef zero "fallback-object"

fallbackCandidateRef : CandidateRef
fallbackCandidateRef =
  candidateRef zero "fallback-candidate"

fallbackEvidenceRef : EvidenceRef
fallbackEvidenceRef =
  evidenceRef zero "fallback-evidence"

fallbackIndexRef : IndexRef
fallbackIndexRef =
  indexRef zero "fallback-index"

fallbackVectorCoordinate : VectorCoordinate
fallbackVectorCoordinate =
  vectorCoordinate zero "fallback-coordinate"

fallbackScoreRef : ScoreRef
fallbackScoreRef =
  scoreRef zero "fallback-score"

fallbackRankRef : RankRef
fallbackRankRef =
  rankRef zero "fallback-rank"

------------------------------------------------------------------------
-- Proposal modes and evidence-claim vocabulary.

data VectorProposalMode : Set where
  embeddingProposalMode :
    VectorProposalMode

  spectralProposalMode :
    VectorProposalMode

  proximityProposalMode :
    VectorProposalMode

  rankingProposalMode :
    VectorProposalMode

  arithmeticProposalMode :
    VectorProposalMode

  blendedProposalMode :
    String →
    VectorProposalMode

canonicalVectorProposalModes : List VectorProposalMode
canonicalVectorProposalModes =
  embeddingProposalMode
  ∷ spectralProposalMode
  ∷ proximityProposalMode
  ∷ rankingProposalMode
  ∷ arithmeticProposalMode
  ∷ []

data VectorEvidenceClaimKind : Set where
  coordinateObservationClaim :
    VectorEvidenceClaimKind

  spectralFeatureClaim :
    VectorEvidenceClaimKind

  proximityScoreClaim :
    VectorEvidenceClaimKind

  rankingOrderClaim :
    VectorEvidenceClaimKind

  arithmeticTransportClaim :
    VectorEvidenceClaimKind

  namedVectorEvidenceClaim :
    String →
    VectorEvidenceClaimKind

canonicalVectorEvidenceClaimKinds : List VectorEvidenceClaimKind
canonicalVectorEvidenceClaimKinds =
  coordinateObservationClaim
  ∷ spectralFeatureClaim
  ∷ proximityScoreClaim
  ∷ rankingOrderClaim
  ∷ arithmeticTransportClaim
  ∷ []

record VectorEvidenceClaim : Set where
  constructor vectorEvidenceClaim
  field
    evidenceClaimRef :
      EvidenceRef

    evidenceClaimKind :
      VectorEvidenceClaimKind

    evidenceClaimMode :
      VectorProposalMode

    evidenceClaimObject :
      ObjectRef

    evidenceClaimCoordinate :
      VectorCoordinate

    evidenceClaimProfile :
      String

    evidenceClaimStatement :
      String

    evidenceClaimCandidateOnly :
      Bool

    evidenceClaimCarriesTruthAuthority :
      Bool

    evidenceClaimCarriesSupportAuthority :
      Bool

    evidenceClaimCarriesAdmissibilityAuthority :
      Bool

    evidenceClaimCarriesTradingAuthority :
      Bool

open VectorEvidenceClaim public

record VectorEvidenceClaimNonAuthorityReceipt
  (claim : VectorEvidenceClaim) :
  Set where
  constructor vectorEvidenceClaimNonAuthorityReceipt
  field
    evidenceClaimIsCandidateOnly :
      evidenceClaimCandidateOnly claim ≡ true

    evidenceClaimNoTruthAuthority :
      evidenceClaimCarriesTruthAuthority claim ≡ false

    evidenceClaimNoSupportAuthority :
      evidenceClaimCarriesSupportAuthority claim ≡ false

    evidenceClaimNoAdmissibilityAuthority :
      evidenceClaimCarriesAdmissibilityAuthority claim ≡ false

    evidenceClaimNoTradingAuthority :
      evidenceClaimCarriesTradingAuthority claim ≡ false

open VectorEvidenceClaimNonAuthorityReceipt public

canonicalVectorEvidenceClaim : VectorEvidenceClaim
canonicalVectorEvidenceClaim =
  vectorEvidenceClaim
    fallbackEvidenceRef
    coordinateObservationClaim
    embeddingProposalMode
    fallbackObjectRef
    fallbackVectorCoordinate
    "fallback-profile"
    "candidate-only vector evidence claim"
    true
    false
    false
    false
    false

canonicalVectorEvidenceClaimReceipt :
  VectorEvidenceClaimNonAuthorityReceipt canonicalVectorEvidenceClaim
canonicalVectorEvidenceClaimReceipt =
  vectorEvidenceClaimNonAuthorityReceipt
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Candidate-only hits.

data CandidateHitKind : Set where
  vectorHit :
    CandidateHitKind

  spectralHit :
    CandidateHitKind

  proximityHit :
    CandidateHitKind

  rankingHit :
    CandidateHitKind

  arithmeticHit :
    CandidateHitKind

  namedCandidateHit :
    String →
    CandidateHitKind

canonicalCandidateHitKinds : List CandidateHitKind
canonicalCandidateHitKinds =
  vectorHit
  ∷ spectralHit
  ∷ proximityHit
  ∷ rankingHit
  ∷ arithmeticHit
  ∷ []

record CandidateOnlyHit : Set where
  constructor candidateOnlyHit
  field
    hitCandidateRef :
      CandidateRef

    hitKind :
      CandidateHitKind

    hitProposalMode :
      VectorProposalMode

    hitIndex :
      IndexRef

    hitObject :
      ObjectRef

    hitCoordinate :
      VectorCoordinate

    hitEvidence :
      EvidenceRef

    hitScore :
      ScoreRef

    hitRank :
      RankRef

    hitRankValue :
      Nat

    hitProfile :
      String

    hitCandidateOnly :
      Bool

    hitCarriesTruthAuthority :
      Bool

    hitCarriesSupportAuthority :
      Bool

    hitCarriesAdmissibilityAuthority :
      Bool

    hitCarriesTradingAuthority :
      Bool

open CandidateOnlyHit public

record CandidateOnlyHitReceipt
  (hit : CandidateOnlyHit) :
  Set where
  constructor candidateOnlyHitReceipt
  field
    hitIsCandidateOnly :
      hitCandidateOnly hit ≡ true

    hitNoTruthAuthority :
      hitCarriesTruthAuthority hit ≡ false

    hitNoSupportAuthority :
      hitCarriesSupportAuthority hit ≡ false

    hitNoAdmissibilityAuthority :
      hitCarriesAdmissibilityAuthority hit ≡ false

    hitNoTradingAuthority :
      hitCarriesTradingAuthority hit ≡ false

open CandidateOnlyHitReceipt public

canonicalCandidateOnlyHit : CandidateOnlyHit
canonicalCandidateOnlyHit =
  candidateOnlyHit
    fallbackCandidateRef
    vectorHit
    embeddingProposalMode
    fallbackIndexRef
    fallbackObjectRef
    fallbackVectorCoordinate
    fallbackEvidenceRef
    fallbackScoreRef
    fallbackRankRef
    zero
    "fallback-hit-profile"
    true
    false
    false
    false
    false

canonicalCandidateOnlyHitReceipt :
  CandidateOnlyHitReceipt canonicalCandidateOnlyHit
canonicalCandidateOnlyHitReceipt =
  candidateOnlyHitReceipt
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Proposal rows for vector, spectral, proximity, ranking, and arithmetic
-- lanes.  These are reusable candidate-motion records only.

record VectorProposalRow : Set where
  constructor vectorProposalRow
  field
    proposalRowMode :
      VectorProposalMode

    proposalRowSourceHit :
      CandidateOnlyHit

    proposalRowEvidenceClaim :
      VectorEvidenceClaim

    proposalRowSourceCoordinate :
      VectorCoordinate

    proposalRowTargetCoordinate :
      VectorCoordinate

    proposalRowProposedObject :
      ObjectRef

    proposalRowProfile :
      String

    proposalRowCandidateOnly :
      Bool

    proposalRowCarriesTruthAuthority :
      Bool

    proposalRowCarriesSupportAuthority :
      Bool

    proposalRowCarriesAdmissibilityAuthority :
      Bool

    proposalRowCarriesTradingAuthority :
      Bool

open VectorProposalRow public

record VectorProposalRowReceipt
  (proposal : VectorProposalRow) :
  Set where
  constructor vectorProposalRowReceipt
  field
    proposalRowIsCandidateOnly :
      proposalRowCandidateOnly proposal ≡ true

    proposalRowNoTruthAuthority :
      proposalRowCarriesTruthAuthority proposal ≡ false

    proposalRowNoSupportAuthority :
      proposalRowCarriesSupportAuthority proposal ≡ false

    proposalRowNoAdmissibilityAuthority :
      proposalRowCarriesAdmissibilityAuthority proposal ≡ false

    proposalRowNoTradingAuthority :
      proposalRowCarriesTradingAuthority proposal ≡ false

open VectorProposalRowReceipt public

canonicalVectorProposalRow : VectorProposalRow
canonicalVectorProposalRow =
  vectorProposalRow
    embeddingProposalMode
    canonicalCandidateOnlyHit
    canonicalVectorEvidenceClaim
    fallbackVectorCoordinate
    fallbackVectorCoordinate
    fallbackObjectRef
    "fallback-proposal-profile"
    true
    false
    false
    false
    false

canonicalVectorProposalRowReceipt :
  VectorProposalRowReceipt canonicalVectorProposalRow
canonicalVectorProposalRowReceipt =
  vectorProposalRowReceipt
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Shared non-authority bundle.

record VectorNonAuthorityReceipt : Set where
  constructor vectorNonAuthorityReceipt
  field
    receiptEvidenceClaim :
      VectorEvidenceClaim

    receiptCandidateHit :
      CandidateOnlyHit

    receiptProposalRow :
      VectorProposalRow

    receiptEvidenceClaimBoundary :
      VectorEvidenceClaimNonAuthorityReceipt receiptEvidenceClaim

    receiptCandidateHitBoundary :
      CandidateOnlyHitReceipt receiptCandidateHit

    receiptProposalRowBoundary :
      VectorProposalRowReceipt receiptProposalRow

    receiptStatement :
      String

open VectorNonAuthorityReceipt public

canonicalVectorNonAuthorityReceipt : VectorNonAuthorityReceipt
canonicalVectorNonAuthorityReceipt =
  vectorNonAuthorityReceipt
    canonicalVectorEvidenceClaim
    canonicalCandidateOnlyHit
    canonicalVectorProposalRow
    canonicalVectorEvidenceClaimReceipt
    canonicalCandidateOnlyHitReceipt
    canonicalVectorProposalRowReceipt
    "Vector, spectral, proximity, ranking, and arithmetic records are candidate-only proposal surfaces with no truth, support, admissibility, or trading authority."

vectorNonAuthorityGenericReceipt :
  VectorNonAuthorityReceipt →
  GenericReceipt.GenericReceipt
vectorNonAuthorityGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    "vector non-authority core"
    "DASHI.Interop.VectorNonAuthorityCore"
    "canonicalVectorNonAuthorityReceipt"
    (receiptStatement receipt)
    "vector, spectral, proximity, ranking, and arithmetic rows remain candidate-only proposal surfaces"
    "agda -i . DASHI/Interop/VectorNonAuthorityCore.agda"

canonicalVectorNonAuthorityGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalVectorNonAuthorityGenericReceipt =
  vectorNonAuthorityGenericReceipt canonicalVectorNonAuthorityReceipt

------------------------------------------------------------------------
-- Empty authority lanes.  The eliminators make the boundary explicit for
-- downstream modules that prefer impossibility witnesses over Boolean fields.

data TruthAuthorityFromVector : Set where

truthAuthorityFromVectorImpossible :
  TruthAuthorityFromVector →
  ⊥
truthAuthorityFromVectorImpossible ()

data SupportAuthorityFromVector : Set where

supportAuthorityFromVectorImpossible :
  SupportAuthorityFromVector →
  ⊥
supportAuthorityFromVectorImpossible ()

data AdmissibilityAuthorityFromVector : Set where

admissibilityAuthorityFromVectorImpossible :
  AdmissibilityAuthorityFromVector →
  ⊥
admissibilityAuthorityFromVectorImpossible ()

data TradingAuthorityFromVector : Set where

tradingAuthorityFromVectorImpossible :
  TradingAuthorityFromVector →
  ⊥
tradingAuthorityFromVectorImpossible ()

vectorProposalModeIsNonAuthority :
  VectorProposalMode →
  ⊤-local
vectorProposalModeIsNonAuthority _ =
  tt-local
