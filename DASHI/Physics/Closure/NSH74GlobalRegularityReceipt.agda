module DASHI.Physics.Closure.NSH74GlobalRegularityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent

------------------------------------------------------------------------
-- H^{7/4} global regularity candidate for carrier-structured data.
--
-- This receipt packages the candidate route only.  The three named pieces
-- are recorded as the required formalisation surface: adjacent-only vortex
-- stretching, subcritical dissipation dominance at s > 7/4, and summable
-- flow-preservation error.  It records bounded enstrophy uniformly in depth
-- and a Leray-limit H^{7/4} target as candidates.  Since H^{7/4} is below
-- the Kato H^{5/2} classical threshold, this is not a Clay promotion.

data NSH74ClaimStatus : Set where
  candidate :
    NSH74ClaimStatus

  conditionalCandidate :
    NSH74ClaimStatus

data NSH74Piece : Set where
  adjacentOnlyVortexStretching :
    NSH74Piece

  subcriticalDissipationDominanceAboveH74 :
    NSH74Piece

  summableFlowPreservationError :
    NSH74Piece

canonicalNSH74Pieces :
  List NSH74Piece
canonicalNSH74Pieces =
  adjacentOnlyVortexStretching
  ∷ subcriticalDissipationDominanceAboveH74
  ∷ summableFlowPreservationError
  ∷ []

data NSH74CandidateOutput : Set where
  boundedEnstrophyUniformlyInDepthCandidate :
    NSH74CandidateOutput

  lerayLimitInH74Candidate :
    NSH74CandidateOutput

canonicalNSH74CandidateOutputs :
  List NSH74CandidateOutput
canonicalNSH74CandidateOutputs =
  boundedEnstrophyUniformlyInDepthCandidate
  ∷ lerayLimitInH74Candidate
  ∷ []

data NSH74FormalisationGap : Set where
  vortexStretchingEstimateNeedsFormalProof :
    NSH74FormalisationGap

  subcriticalDissipationDominanceNeedsFormalProof :
    NSH74FormalisationGap

  summableFlowErrorNeedsFormalProof :
    NSH74FormalisationGap

  h74LerayLimitPassageNeedsFormalProof :
    NSH74FormalisationGap

canonicalNSH74FormalisationGaps :
  List NSH74FormalisationGap
canonicalNSH74FormalisationGaps =
  vortexStretchingEstimateNeedsFormalProof
  ∷ subcriticalDissipationDominanceNeedsFormalProof
  ∷ summableFlowErrorNeedsFormalProof
  ∷ h74LerayLimitPassageNeedsFormalProof
  ∷ []

data NSH74GlobalRegularityPromotion : Set where

nsH74GlobalRegularityPromotionImpossibleHere :
  NSH74GlobalRegularityPromotion →
  ⊥
nsH74GlobalRegularityPromotionImpossibleHere ()

nsH74GlobalRegularityStatement : String
nsH74GlobalRegularityStatement =
  "H74 Navier-Stokes carrier route: candidate only.  The route needs three formal pieces: adjacent-only vortex stretching, subcritical dissipation dominance for s > 7/4, and summable flow-preservation error.  It records bounded enstrophy uniformly in depth and a Leray limit in H^{7/4} as candidates.  H^{7/4} is below the Kato H^{5/2} threshold, so below-threshold regularity is conditional-candidate only and no Clay promotion is made."

record NSH74GlobalRegularityReceipt : Setω where
  field
    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyReceiptCandidate :
      Adjacent.vortexStretchingNearestNeighbourScaleLatticeCandidate
        adjacentOnlyReceipt
      ≡
      true

    adjacentOnlyReceiptNoClay :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt ≡ false

    adjacentOnlyReceiptNoGlobalPromotion :
      Adjacent.globalRegularityPromoted adjacentOnlyReceipt ≡ false

    pieces :
      List NSH74Piece

    piecesAreCanonical :
      pieces ≡ canonicalNSH74Pieces

    allThreePiecesRecorded :
      Bool

    allThreePiecesRecordedIsTrue :
      allThreePiecesRecorded ≡ true

    adjacentOnlyVortexStretchingRecorded :
      Bool

    adjacentOnlyVortexStretchingRecordedIsTrue :
      adjacentOnlyVortexStretchingRecorded ≡ true

    subcriticalDissipationDominanceAtS>7/4 :
      Bool

    subcriticalDissipationDominanceAtS>7/4IsTrue :
      subcriticalDissipationDominanceAtS>7/4 ≡ true

    summableFlowPreservationErrorRecorded :
      Bool

    summableFlowPreservationErrorRecordedIsTrue :
      summableFlowPreservationErrorRecorded ≡ true

    threePiecesNeedFormalisation :
      Bool

    threePiecesNeedFormalisationIsTrue :
      threePiecesNeedFormalisation ≡ true

    formalisationGaps :
      List NSH74FormalisationGap

    formalisationGapsAreCanonical :
      formalisationGaps ≡ canonicalNSH74FormalisationGaps

    boundedEnstrophyUniformlyInDepth :
      NSH74ClaimStatus

    boundedEnstrophyUniformlyInDepthIsCandidate :
      boundedEnstrophyUniformlyInDepth ≡ candidate

    lerayLimitInH74 :
      NSH74ClaimStatus

    lerayLimitInH74IsCandidate :
      lerayLimitInH74 ≡ candidate

    candidateOutputs :
      List NSH74CandidateOutput

    candidateOutputsAreCanonical :
      candidateOutputs ≡ canonicalNSH74CandidateOutputs

    h74SobolevNumerator :
      Nat

    h74SobolevNumeratorIs7 :
      h74SobolevNumerator ≡ 7

    h74SobolevDenominator :
      Nat

    h74SobolevDenominatorIs4 :
      h74SobolevDenominator ≡ 4

    katoThresholdNumerator :
      Nat

    katoThresholdNumeratorIs5 :
      katoThresholdNumerator ≡ 5

    katoThresholdDenominator :
      Nat

    katoThresholdDenominatorIs2 :
      katoThresholdDenominator ≡ 2

    belowKatoThreshold5/2 :
      Bool

    belowKatoThreshold5/2IsTrue :
      belowKatoThreshold5/2 ≡ true

    nsH74GlobalRegularity :
      NSH74ClaimStatus

    nsH74GlobalRegularityIsCandidate :
      nsH74GlobalRegularity ≡ candidate

    nsRegularityBelowKato :
      NSH74ClaimStatus

    nsRegularityBelowKatoIsConditionalCandidate :
      nsRegularityBelowKato ≡ conditionalCandidate

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayPromotionAttempted :
      Bool

    clayPromotionAttemptedIsFalse :
      clayPromotionAttempted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsH74GlobalRegularityStatement

    promotionFlags :
      List NSH74GlobalRegularityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSH74GlobalRegularityReceipt public

canonicalNSH74GlobalRegularityReceipt :
  NSH74GlobalRegularityReceipt
canonicalNSH74GlobalRegularityReceipt =
  record
    { adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyReceiptCandidate =
        refl
    ; adjacentOnlyReceiptNoClay =
        refl
    ; adjacentOnlyReceiptNoGlobalPromotion =
        refl
    ; pieces =
        canonicalNSH74Pieces
    ; piecesAreCanonical =
        refl
    ; allThreePiecesRecorded =
        true
    ; allThreePiecesRecordedIsTrue =
        refl
    ; adjacentOnlyVortexStretchingRecorded =
        true
    ; adjacentOnlyVortexStretchingRecordedIsTrue =
        refl
    ; subcriticalDissipationDominanceAtS>7/4 =
        true
    ; subcriticalDissipationDominanceAtS>7/4IsTrue =
        refl
    ; summableFlowPreservationErrorRecorded =
        true
    ; summableFlowPreservationErrorRecordedIsTrue =
        refl
    ; threePiecesNeedFormalisation =
        true
    ; threePiecesNeedFormalisationIsTrue =
        refl
    ; formalisationGaps =
        canonicalNSH74FormalisationGaps
    ; formalisationGapsAreCanonical =
        refl
    ; boundedEnstrophyUniformlyInDepth =
        candidate
    ; boundedEnstrophyUniformlyInDepthIsCandidate =
        refl
    ; lerayLimitInH74 =
        candidate
    ; lerayLimitInH74IsCandidate =
        refl
    ; candidateOutputs =
        canonicalNSH74CandidateOutputs
    ; candidateOutputsAreCanonical =
        refl
    ; h74SobolevNumerator =
        7
    ; h74SobolevNumeratorIs7 =
        refl
    ; h74SobolevDenominator =
        4
    ; h74SobolevDenominatorIs4 =
        refl
    ; katoThresholdNumerator =
        5
    ; katoThresholdNumeratorIs5 =
        refl
    ; katoThresholdDenominator =
        2
    ; katoThresholdDenominatorIs2 =
        refl
    ; belowKatoThreshold5/2 =
        true
    ; belowKatoThreshold5/2IsTrue =
        refl
    ; nsH74GlobalRegularity =
        candidate
    ; nsH74GlobalRegularityIsCandidate =
        refl
    ; nsRegularityBelowKato =
        conditionalCandidate
    ; nsRegularityBelowKatoIsConditionalCandidate =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayPromotionAttempted =
        false
    ; clayPromotionAttemptedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; statement =
        nsH74GlobalRegularityStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "nsH74GlobalRegularity = candidate"
        ∷ "threePiecesNeedFormalisation = true"
        ∷ "belowKatoThreshold5/2 = true"
        ∷ "nsRegularityBelowKato = conditional candidate"
        ∷ "bounded enstrophy uniformly in depth is recorded only as candidate"
        ∷ "Leray limit in H^{7/4} is recorded only as candidate"
        ∷ "No Clay Navier-Stokes promotion is made"
        ∷ []
    }

canonicalNSH74GlobalRegularityIsCandidate :
  nsH74GlobalRegularity canonicalNSH74GlobalRegularityReceipt ≡ candidate
canonicalNSH74GlobalRegularityIsCandidate =
  refl

canonicalThreePiecesNeedFormalisationTrue :
  threePiecesNeedFormalisation canonicalNSH74GlobalRegularityReceipt ≡ true
canonicalThreePiecesNeedFormalisationTrue =
  refl

canonicalBelowKatoThreshold5/2True :
  belowKatoThreshold5/2 canonicalNSH74GlobalRegularityReceipt ≡ true
canonicalBelowKatoThreshold5/2True =
  refl

canonicalNSRegularityBelowKatoConditionalCandidate :
  nsRegularityBelowKato canonicalNSH74GlobalRegularityReceipt
  ≡
  conditionalCandidate
canonicalNSRegularityBelowKatoConditionalCandidate =
  refl

nsH74GlobalRegularityDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSH74GlobalRegularityReceipt ≡ false
nsH74GlobalRegularityDoesNotPromoteClay =
  refl

nsH74GlobalRegularityNoPromotion :
  NSH74GlobalRegularityPromotion →
  ⊥
nsH74GlobalRegularityNoPromotion =
  nsH74GlobalRegularityPromotionImpossibleHere
