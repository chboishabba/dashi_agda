module DASHI.Physics.Boundaries.GribovResolutionAuthorityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- External candidate: Cambridge Open Engage Agawa Gribov addendum.
--
-- The source is a retracted, non-peer-reviewed working paper.  It is
-- recorded as a candidate authority receipt and remains non-promoting.  It
-- cannot supply continuum Gribov-copy resolution, defeat Singer's global
-- smooth-section obstruction, close Gate3/continuum lift, or promote Clay YM.

data GribovResolutionAuthorityBlocker : Set where
  cambridgeEngageRetracted :
    GribovResolutionAuthorityBlocker

  workingPaperNotPeerReviewed :
    GribovResolutionAuthorityBlocker

  noAcceptedGribovUniquenessTheorem :
    GribovResolutionAuthorityBlocker

  continuumGribovCopiesUnresolved :
    GribovResolutionAuthorityBlocker

  singerGlobalSectionObstructionUnresolved :
    GribovResolutionAuthorityBlocker

  gate3ContinuumLiftOpen :
    GribovResolutionAuthorityBlocker

  supersededRGAndMorseRouteWithdrawn :
    GribovResolutionAuthorityBlocker

  noClayAcceptance :
    GribovResolutionAuthorityBlocker

  noInternalFormalImport :
    GribovResolutionAuthorityBlocker

canonicalGribovResolutionAuthorityBlockers :
  List GribovResolutionAuthorityBlocker
canonicalGribovResolutionAuthorityBlockers =
  cambridgeEngageRetracted
  ∷ workingPaperNotPeerReviewed
  ∷ noAcceptedGribovUniquenessTheorem
  ∷ continuumGribovCopiesUnresolved
  ∷ singerGlobalSectionObstructionUnresolved
  ∷ gate3ContinuumLiftOpen
  ∷ supersededRGAndMorseRouteWithdrawn
  ∷ noClayAcceptance
  ∷ noInternalFormalImport
  ∷ []

record GribovResolutionAuthorityReceipt : Setω where
  field
    sourceIdentifier :
      String

    sourceIdentifierIsCanonical :
      sourceIdentifier
      ≡
      "Cambridge Open Engage coe-2025-3jmcf, Version 2 (Retracted)"

    sourceDOI :
      String

    sourceDOIIsCanonical :
      sourceDOI ≡ "10.33774/coe-2025-3jmcf"

    upstreamAgawaDOI :
      String

    upstreamAgawaDOIIsCanonical :
      upstreamAgawaDOI ≡ "10.5281/zenodo.14975444"

    sourceTitle :
      String

    sourceTitleIsCanonical :
      sourceTitle
      ≡
      "On the Completion of Agawa's Proof of the Yang-Mills Mass Gap: The Essential Addendum on the Continuum Limit and Finite Gribov Uniqueness"

    authorityStatus :
      String

    authorityStatusIsCanonical :
      authorityStatus
      ≡
      "retracted by the author; Working Paper; not peer-reviewed by Cambridge University Press at time of posting"

    gribovRoute :
      String

    gribovRouteIsCanonical :
      gribovRoute
      ≡
      "external finite/candidate Gribov-copy uniqueness claim recorded only; continuum copies remain unresolved"

    morseRoute :
      String

    morseRouteIsCanonical :
      morseRoute
      ≡
      "v1 attempted Morse theory for finite Gribov problem and was formally withdrawn"

    rgRoute :
      String

    rgRouteIsCanonical :
      rgRoute
      ≡
      "v1 attempted RG analysis for continuum limit and was superseded after self-review"

    candidateEvidenceRecorded :
      Bool

    candidateEvidenceRecordedIsTrue :
      candidateEvidenceRecorded ≡ true

    sourceAuthorityAccepted :
      Bool

    sourceAuthorityAcceptedIsFalse :
      sourceAuthorityAccepted ≡ false

    gribovResolutionPromoted :
      Bool

    gribovResolutionPromotedIsFalse :
      gribovResolutionPromoted ≡ false

    continuumGribovCopiesResolved :
      Bool

    continuumGribovCopiesResolvedIsFalse :
      continuumGribovCopiesResolved ≡ false

    singerGlobalSectionObstructionDefeated :
      Bool

    singerGlobalSectionObstructionDefeatedIsFalse :
      singerGlobalSectionObstructionDefeated ≡ false

    gate3ContinuumLiftClosed :
      Bool

    gate3ContinuumLiftClosedIsFalse :
      gate3ContinuumLiftClosed ≡ false

    theoremClosurePromoted :
      Bool

    theoremClosurePromotedIsFalse :
      theoremClosurePromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    canonicalBlockers :
      List GribovResolutionAuthorityBlocker

    canonicalBlockersAreCanonical :
      canonicalBlockers ≡ canonicalGribovResolutionAuthorityBlockers

    receiptNotes :
      List String

open GribovResolutionAuthorityReceipt public

canonicalGribovResolutionAuthorityReceipt :
  GribovResolutionAuthorityReceipt
canonicalGribovResolutionAuthorityReceipt =
  record
    { sourceIdentifier =
        "Cambridge Open Engage coe-2025-3jmcf, Version 2 (Retracted)"
    ; sourceIdentifierIsCanonical =
        refl
    ; sourceDOI =
        "10.33774/coe-2025-3jmcf"
    ; sourceDOIIsCanonical =
        refl
    ; upstreamAgawaDOI =
        "10.5281/zenodo.14975444"
    ; upstreamAgawaDOIIsCanonical =
        refl
    ; sourceTitle =
        "On the Completion of Agawa's Proof of the Yang-Mills Mass Gap: The Essential Addendum on the Continuum Limit and Finite Gribov Uniqueness"
    ; sourceTitleIsCanonical =
        refl
    ; authorityStatus =
        "retracted by the author; Working Paper; not peer-reviewed by Cambridge University Press at time of posting"
    ; authorityStatusIsCanonical =
        refl
    ; gribovRoute =
        "external finite/candidate Gribov-copy uniqueness claim recorded only; continuum copies remain unresolved"
    ; gribovRouteIsCanonical =
        refl
    ; morseRoute =
        "v1 attempted Morse theory for finite Gribov problem and was formally withdrawn"
    ; morseRouteIsCanonical =
        refl
    ; rgRoute =
        "v1 attempted RG analysis for continuum limit and was superseded after self-review"
    ; rgRouteIsCanonical =
        refl
    ; candidateEvidenceRecorded =
        true
    ; candidateEvidenceRecordedIsTrue =
        refl
    ; sourceAuthorityAccepted =
        false
    ; sourceAuthorityAcceptedIsFalse =
        refl
    ; gribovResolutionPromoted =
        false
    ; gribovResolutionPromotedIsFalse =
        refl
    ; continuumGribovCopiesResolved =
        false
    ; continuumGribovCopiesResolvedIsFalse =
        refl
    ; singerGlobalSectionObstructionDefeated =
        false
    ; singerGlobalSectionObstructionDefeatedIsFalse =
        refl
    ; gate3ContinuumLiftClosed =
        false
    ; gate3ContinuumLiftClosedIsFalse =
        refl
    ; theoremClosurePromoted =
        false
    ; theoremClosurePromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; canonicalBlockers =
        canonicalGribovResolutionAuthorityBlockers
    ; canonicalBlockersAreCanonical =
        refl
    ; receiptNotes =
        "Recorded as external candidate evidence only"
        ∷ "Retraction and non-peer-reviewed working-paper status block Gribov or Clay promotion"
        ∷ "Continuum Gribov copies persist unless separately handled; this receipt supplies no continuum gauge-slice theorem"
        ∷ "Singer's theorem/global smooth gauge-section obstruction is not defeated by this authority receipt"
        ∷ "Gate3/continuum lift remains open"
        ∷ "The prior Morse/RG route is explicitly retained as withdrawn historical route evidence"
        ∷ []
    }
