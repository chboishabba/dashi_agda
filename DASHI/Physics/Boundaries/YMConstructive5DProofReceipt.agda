module DASHI.Physics.Boundaries.YMConstructive5DProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- External candidate: arXiv:2506.00284.
--
-- Governance lookup records this source as withdrawn by arXiv Admin.  The
-- proof route is recorded as evidence only; it cannot promote Gate 2 or Clay
-- Yang-Mills closure.

data YMConstructive5DProofBlocker : Set where
  arxivAdminWithdrawn :
    YMConstructive5DProofBlocker

  noAvailableAcceptedPeerReview :
    YMConstructive5DProofBlocker

  noClayAcceptance :
    YMConstructive5DProofBlocker

  noInternalFormalImport :
    YMConstructive5DProofBlocker

  noContinuumWightmanOSCertificate :
    YMConstructive5DProofBlocker

  noTransferMatrixSpectralProjectionCertificate :
    YMConstructive5DProofBlocker

canonicalYMConstructive5DProofBlockers :
  List YMConstructive5DProofBlocker
canonicalYMConstructive5DProofBlockers =
  arxivAdminWithdrawn
  ∷ noAvailableAcceptedPeerReview
  ∷ noClayAcceptance
  ∷ noInternalFormalImport
  ∷ noContinuumWightmanOSCertificate
  ∷ noTransferMatrixSpectralProjectionCertificate
  ∷ []

record YMConstructive5DProofReceipt : Setω where
  field
    sourceIdentifier :
      String

    sourceIdentifierIsCanonical :
      sourceIdentifier ≡ "arXiv:2506.00284v2 [physics.gen-ph]"

    sourceDOI :
      String

    sourceDOIIsCanonical :
      sourceDOI ≡ "10.48550/arXiv.2506.00284"

    sourceTitle :
      String

    sourceTitleIsCanonical :
      sourceTitle
      ≡
      "A Constructive Proof of Existence and Mass Gap for Pure SU(3) Yang-Mills in Four-Dimensional Space-Time"

    authorityStatus :
      String

    authorityStatusIsCanonical :
      authorityStatus
      ≡
      "withdrawn by arXiv Admin; arXiv admin note: does not meet arXiv research content quality standards"

    polymerRoute :
      String

    polymerRouteIsCanonical :
      polymerRoute
      ≡
      "convergent joint polymer expansion on Wilson lattice claimed for a->0 and L->infinity"

    osRoute :
      String

    osRouteIsCanonical :
      osRoute
      ≡
      "Osterwalder-Schrader reconstruction route claimed for unique-vacuum Wightman theory"

    transferMatrixRoute :
      String

    transferMatrixRouteIsCanonical :
      transferMatrixRoute
      ≡
      "Sturm-Liouville five-dimensional fluctuation analysis plus transfer-matrix spectral projections"

    candidateEvidenceRecorded :
      Bool

    candidateEvidenceRecordedIsTrue :
      candidateEvidenceRecorded ≡ true

    sourceAuthorityAccepted :
      Bool

    sourceAuthorityAcceptedIsFalse :
      sourceAuthorityAccepted ≡ false

    theoremClosurePromoted :
      Bool

    theoremClosurePromotedIsFalse :
      theoremClosurePromoted ≡ false

    gate2Promoted :
      Bool

    gate2PromotedIsFalse :
      gate2Promoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    canonicalBlockers :
      List YMConstructive5DProofBlocker

    canonicalBlockersAreCanonical :
      canonicalBlockers ≡ canonicalYMConstructive5DProofBlockers

    receiptNotes :
      List String

open YMConstructive5DProofReceipt public

canonicalYMConstructive5DProofReceipt :
  YMConstructive5DProofReceipt
canonicalYMConstructive5DProofReceipt =
  record
    { sourceIdentifier =
        "arXiv:2506.00284v2 [physics.gen-ph]"
    ; sourceIdentifierIsCanonical =
        refl
    ; sourceDOI =
        "10.48550/arXiv.2506.00284"
    ; sourceDOIIsCanonical =
        refl
    ; sourceTitle =
        "A Constructive Proof of Existence and Mass Gap for Pure SU(3) Yang-Mills in Four-Dimensional Space-Time"
    ; sourceTitleIsCanonical =
        refl
    ; authorityStatus =
        "withdrawn by arXiv Admin; arXiv admin note: does not meet arXiv research content quality standards"
    ; authorityStatusIsCanonical =
        refl
    ; polymerRoute =
        "convergent joint polymer expansion on Wilson lattice claimed for a->0 and L->infinity"
    ; polymerRouteIsCanonical =
        refl
    ; osRoute =
        "Osterwalder-Schrader reconstruction route claimed for unique-vacuum Wightman theory"
    ; osRouteIsCanonical =
        refl
    ; transferMatrixRoute =
        "Sturm-Liouville five-dimensional fluctuation analysis plus transfer-matrix spectral projections"
    ; transferMatrixRouteIsCanonical =
        refl
    ; candidateEvidenceRecorded =
        true
    ; candidateEvidenceRecordedIsTrue =
        refl
    ; sourceAuthorityAccepted =
        false
    ; sourceAuthorityAcceptedIsFalse =
        refl
    ; theoremClosurePromoted =
        false
    ; theoremClosurePromotedIsFalse =
        refl
    ; gate2Promoted =
        false
    ; gate2PromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; canonicalBlockers =
        canonicalYMConstructive5DProofBlockers
    ; canonicalBlockersAreCanonical =
        refl
    ; receiptNotes =
        "Recorded as external candidate evidence only"
        ∷ "Withdrawal status blocks promotion regardless of claimed polymer, OS, and transfer-matrix route"
        ∷ "No Gate 2 selected-carrier theorem, continuum theorem, or Clay acceptance is introduced"
        ∷ []
    }
