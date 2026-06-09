module DASHI.Physics.Closure.YMExternal2025To2026ProofClaimsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- External 2025-2026 Yang-Mills proof-claim intake receipt.
--
-- This receipt records the existence of external proof claims only as
-- unreviewed external claims.  It does not certify authority, import a proof,
-- or promote any Clay Yang-Mills result.

data YMExternalProofClaimWindow : Set where
  external2025To2026 :
    YMExternalProofClaimWindow

data YMExternalProofClaimStatus : Set where
  unreviewedExternalClaim :
    YMExternalProofClaimStatus

data YMExternalProofClaim : Set where
  arxiv250600284WithdrawnFiveDOrbifoldClaim :
    YMExternalProofClaim

  yangmillsDevMachineVerifiedBalabanClaim :
    YMExternalProofClaim

  cambridgeEngageRetractedHolonomyClusterClaim :
    YMExternalProofClaim

  externalYMExistenceAndMassGapClaim :
    YMExternalProofClaim

  externalYMConstructionClaim :
    YMExternalProofClaim

  externalYMMassGapEstimateClaim :
    YMExternalProofClaim

canonicalYMExternal2025To2026Claims : List YMExternalProofClaim
canonicalYMExternal2025To2026Claims =
  arxiv250600284WithdrawnFiveDOrbifoldClaim
  ∷ yangmillsDevMachineVerifiedBalabanClaim
  ∷ cambridgeEngageRetractedHolonomyClusterClaim
  ∷ externalYMExistenceAndMassGapClaim
  ∷ externalYMConstructionClaim
  ∷ externalYMMassGapEstimateClaim
  ∷ []

data YMExternalProofClaimPromotion : Set where

ymExternalProofClaimPromotionImpossibleHere :
  YMExternalProofClaimPromotion →
  ⊥
ymExternalProofClaimPromotionImpossibleHere ()

ymExternal2025To2026ClaimStatement : String
ymExternal2025To2026ClaimStatement =
  "External 2025-2026 Yang-Mills proof claims are recorded only as unreviewed external claims; no DASHI formal import, authority acceptance, Clay Yang-Mills proof, or terminal promotion is made."

record YMExternal2025To2026ProofClaimsReceipt : Setω where
  field
    claimWindow :
      YMExternalProofClaimWindow

    claimWindowIsCanonical :
      claimWindow ≡ external2025To2026

    claimStatus :
      YMExternalProofClaimStatus

    claimStatusIsUnreviewedExternal :
      claimStatus ≡ unreviewedExternalClaim

    sourceClass :
      String

    sourceClassIsCanonical :
      sourceClass ≡ "external 2025-2026 Yang-Mills proof claims"

    claims :
      List YMExternalProofClaim

    claimsAreCanonical :
      claims ≡ canonicalYMExternal2025To2026Claims

    recordedAsExternalClaims :
      Bool

    recordedAsExternalClaimsIsTrue :
      recordedAsExternalClaims ≡ true

    arxiv250600284WithdrawnByArxivAdmin :
      Bool

    arxiv250600284WithdrawnByArxivAdminIsTrue :
      arxiv250600284WithdrawnByArxivAdmin ≡ true

    yangmillsDevClayAccepted :
      Bool

    yangmillsDevClayAcceptedIsFalse :
      yangmillsDevClayAccepted ≡ false

    cambridgeEngageRetracted :
      Bool

    cambridgeEngageRetractedIsTrue :
      cambridgeEngageRetracted ≡ true

    cambridgeEngagePeerReviewed :
      Bool

    cambridgeEngagePeerReviewedIsFalse :
      cambridgeEngagePeerReviewed ≡ false

    reviewedByDASHI :
      Bool

    reviewedByDASHIIsFalse :
      reviewedByDASHI ≡ false

    authorityAccepted :
      Bool

    authorityAcceptedIsFalse :
      authorityAccepted ≡ false

    formalProofImported :
      Bool

    formalProofImportedIsFalse :
      formalProofImported ≡ false

    theoremClosurePromoted :
      Bool

    theoremClosurePromotedIsFalse :
      theoremClosurePromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List YMExternalProofClaimPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ ymExternal2025To2026ClaimStatement

    receiptBoundary :
      List String

open YMExternal2025To2026ProofClaimsReceipt public

canonicalYMExternal2025To2026ProofClaimsReceipt :
  YMExternal2025To2026ProofClaimsReceipt
canonicalYMExternal2025To2026ProofClaimsReceipt =
  record
    { claimWindow =
        external2025To2026
    ; claimWindowIsCanonical =
        refl
    ; claimStatus =
        unreviewedExternalClaim
    ; claimStatusIsUnreviewedExternal =
        refl
    ; sourceClass =
        "external 2025-2026 Yang-Mills proof claims"
    ; sourceClassIsCanonical =
        refl
    ; claims =
        canonicalYMExternal2025To2026Claims
    ; claimsAreCanonical =
        refl
    ; recordedAsExternalClaims =
        true
    ; recordedAsExternalClaimsIsTrue =
        refl
    ; arxiv250600284WithdrawnByArxivAdmin =
        true
    ; arxiv250600284WithdrawnByArxivAdminIsTrue =
        refl
    ; yangmillsDevClayAccepted =
        false
    ; yangmillsDevClayAcceptedIsFalse =
        refl
    ; cambridgeEngageRetracted =
        true
    ; cambridgeEngageRetractedIsTrue =
        refl
    ; cambridgeEngagePeerReviewed =
        false
    ; cambridgeEngagePeerReviewedIsFalse =
        refl
    ; reviewedByDASHI =
        false
    ; reviewedByDASHIIsFalse =
        refl
    ; authorityAccepted =
        false
    ; authorityAcceptedIsFalse =
        refl
    ; formalProofImported =
        false
    ; formalProofImportedIsFalse =
        refl
    ; theoremClosurePromoted =
        false
    ; theoremClosurePromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        ymExternal2025To2026ClaimStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "arXiv:2506.00284 is recorded as a withdrawn 5D-orbifold proof claim, not authority"
        ∷ "yangmills.dev is recorded as a self-hosted machine-verification claim, not Clay acceptance"
        ∷ "The Cambridge Engage holonomy/cluster claim is recorded as retracted and non-peer-reviewed"
        ∷ "Unreviewed external proof claims are intake metadata only"
        ∷ "No external authority acceptance or peer-review acceptance is recorded here"
        ∷ "No formal proof is imported into DASHI by this receipt"
        ∷ "No Clay Yang-Mills, mass-gap, theorem-closure, or terminal promotion is made"
        ∷ []
    }

ymExternal2025To2026KeepsClayFalse :
  clayYangMillsPromoted canonicalYMExternal2025To2026ProofClaimsReceipt ≡ false
ymExternal2025To2026KeepsClayFalse =
  refl

ymExternal2025To2026KeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYMExternal2025To2026ProofClaimsReceipt ≡ false
ymExternal2025To2026KeepsTerminalFalse =
  refl
