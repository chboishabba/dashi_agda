module DASHI.Physics.Closure.NSCandidateCompleteEnstrophyBKMPassageReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Clay
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap
import DASHI.Physics.Closure.NSRegularityRoadmapFilledReceipt as Roadmap

------------------------------------------------------------------------
-- Candidate-complete enstrophy/BKM passage receipt.
--
-- This receipt is intentionally bounded: it records the candidate NS-side
-- passage grammar around enstrophy, vorticity, BKM, and global regularity
-- without promoting any Clay-facing claim.  The shared Clay target receipt
-- still keeps the uniform vorticity and continuum BKM passages false.

data NSCandidateCompleteEnstrophyBKMPassageStatus : Set where
  candidateCompletePassageRecordedWithoutPromotion :
    NSCandidateCompleteEnstrophyBKMPassageStatus

data NSCandidateCompleteEnstrophyBKMPassageFlag : Set where
  candidatePacketRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  finiteDepthRegularityRungsRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  enstrophyPassageCandidateRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  vorticityPassageCandidateRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  bkmPassageCandidateRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  globalRegularityPassageCandidateRecorded :
    NSCandidateCompleteEnstrophyBKMPassageFlag

  clayPromotionStillFalse :
    NSCandidateCompleteEnstrophyBKMPassageFlag

canonicalNSCandidateCompleteEnstrophyBKMPassageFlags :
  List NSCandidateCompleteEnstrophyBKMPassageFlag
canonicalNSCandidateCompleteEnstrophyBKMPassageFlags =
  candidatePacketRecorded
  ∷ finiteDepthRegularityRungsRecorded
  ∷ enstrophyPassageCandidateRecorded
  ∷ vorticityPassageCandidateRecorded
  ∷ bkmPassageCandidateRecorded
  ∷ globalRegularityPassageCandidateRecorded
  ∷ clayPromotionStillFalse
  ∷ []

data NSCandidateCompleteEnstrophyBKMPassagePromotion : Set where

nsCandidateCompleteEnstrophyBKMNoPromotion :
  NSCandidateCompleteEnstrophyBKMPassagePromotion →
  ⊥
nsCandidateCompleteEnstrophyBKMNoPromotion ()

nsCandidateCompleteEnstrophyBKMPassageStatement : String
nsCandidateCompleteEnstrophyBKMPassageStatement =
  "Candidate-complete NS passage surface: the enstrophy, vorticity, BKM, and global-regularity grammar is recorded as a bounded receipt, but the Clay-facing uniform vorticity and continuum BKM passages remain false and no promotion is made."

record NSCandidateCompleteEnstrophyBKMPassageReceipt : Setω where
  field
    status :
      NSCandidateCompleteEnstrophyBKMPassageStatus

    statusIsCanonical :
      status ≡ candidateCompletePassageRecordedWithoutPromotion

    roadmapReceipt :
      Roadmap.NSRegularityRoadmapFilledReceipt

    roadmapFilled :
      Roadmap.roadmapFilled roadmapReceipt ≡ true

    gapReceipt :
      Gap.NSRegularityGapReceipt

    candidateSelfContainedPacketRecorded :
      Gap.candidateSelfContainedPacketRecorded gapReceipt ≡ true

    gapFiniteDepthRegularityRungsRecorded :
      Gap.finiteDepthRegularityRungsRecorded gapReceipt ≡ true

    globalSmoothRegularityProved :
      Gap.globalSmoothRegularityProved gapReceipt ≡ false

    bkmVorticityControlClosed :
      Gap.bkmVorticityControlClosed gapReceipt ≡ false

    clayTargetReceipt :
      Clay.CarrierBKMControlTargetReceipt

    clayTargetFrontierKind :
      Clay.frontierKind clayTargetReceipt
      ≡
      Clay.candidateCompletePendingPromotionEvidence

    uniformVorticityLInfinityControlConstructed :
      Clay.uniformVorticityLInfinityControlConstructed clayTargetReceipt
      ≡
      false

    continuumBKMRegularityPassageConstructed :
      Clay.continuumBKMRegularityPassageConstructed clayTargetReceipt
      ≡
      false

    clayNavierStokesClosed :
      Clay.clayNavierStokesClosed clayTargetReceipt ≡ false

    candidateFlags :
      List NSCandidateCompleteEnstrophyBKMPassageFlag

    candidateFlagsAreCanonical :
      candidateFlags ≡ canonicalNSCandidateCompleteEnstrophyBKMPassageFlags

    candidateCompletePassageRecorded :
      Bool

    candidateCompletePassageRecordedIsTrue :
      candidateCompletePassageRecorded ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCandidateCompleteEnstrophyBKMPassageStatement

    promotionFlags :
      List NSCandidateCompleteEnstrophyBKMPassagePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCandidateCompleteEnstrophyBKMPassageReceipt public

canonicalNSCandidateCompleteEnstrophyBKMPassageReceipt :
  NSCandidateCompleteEnstrophyBKMPassageReceipt
canonicalNSCandidateCompleteEnstrophyBKMPassageReceipt =
  record
    { status =
        candidateCompletePassageRecordedWithoutPromotion
    ; statusIsCanonical =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalNSRegularityRoadmapFilledReceipt
    ; roadmapFilled =
        refl
    ; gapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; candidateSelfContainedPacketRecorded =
        refl
    ; gapFiniteDepthRegularityRungsRecorded =
        refl
    ; globalSmoothRegularityProved =
        refl
    ; bkmVorticityControlClosed =
        refl
    ; clayTargetReceipt =
        Clay.canonicalCarrierBKMControlTargetReceipt
    ; clayTargetFrontierKind =
        refl
    ; uniformVorticityLInfinityControlConstructed =
        refl
    ; continuumBKMRegularityPassageConstructed =
        refl
    ; clayNavierStokesClosed =
        refl
    ; candidateFlags =
        canonicalNSCandidateCompleteEnstrophyBKMPassageFlags
    ; candidateFlagsAreCanonical =
        refl
    ; candidateCompletePassageRecorded =
        true
    ; candidateCompletePassageRecordedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsCandidateCompleteEnstrophyBKMPassageStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The NS candidate packet is now surfaced as an explicit enstrophy/vorticity/BKM/global-regularity passage receipt"
        ∷ "The route is bounded by the existing NS regularity roadmap and gap receipts, not by any Clay promotion"
        ∷ "The Clay target receipt still keeps uniform vorticity-Linf control, continuum BKM passage, and Clay closure false"
        ∷ "No promotion flags are introduced by this receipt"
        ∷ []
    }

nsCandidateCompleteEnstrophyBKMPassageKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCandidateCompleteEnstrophyBKMPassageReceipt
  ≡
  false
nsCandidateCompleteEnstrophyBKMPassageKeepsClayFalse =
  refl
