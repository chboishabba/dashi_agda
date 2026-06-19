module DASHI.Physics.Closure.NSBroadTubeSerrinLiftGapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Calc 8 / weighted lambda2 broad-tube Serrin lift gap receipt.
--
-- This receipt records that the Calc 8 weighted lambda2 evidence makes the
-- strict carrier lane insufficient.  The remaining live gap is the broad-tube
-- Serrin lift / interior continuation route, with coarea, Serrin lift, and
-- BKM bridge obligations left open and no Clay promotion claimed here.

data NSBroadTubeSerrinLiftGapStatus : Set where
  calc8WeightedLambda2MakesStrictCarrierInsufficient :
    NSBroadTubeSerrinLiftGapStatus

data NSBroadTubeSerrinEvidence : Set where
  calc8WeightedLambda2EvidenceRecorded :
    NSBroadTubeSerrinEvidence

  strictCarrierLaneInsufficientRecorded :
    NSBroadTubeSerrinEvidence

  broadTubeInteriorContinuationOpen :
    NSBroadTubeSerrinEvidence

  serrinLiftRouteRequired :
    NSBroadTubeSerrinEvidence

canonicalNSBroadTubeSerrinEvidence :
  List NSBroadTubeSerrinEvidence
canonicalNSBroadTubeSerrinEvidence =
  calc8WeightedLambda2EvidenceRecorded
  ∷ strictCarrierLaneInsufficientRecorded
  ∷ broadTubeInteriorContinuationOpen
  ∷ serrinLiftRouteRequired
  ∷ []

data NSBroadTubeSerrinLiveGapItem : Set where
  broadTubeCoarea :
    NSBroadTubeSerrinLiveGapItem

  serrinLift :
    NSBroadTubeSerrinLiveGapItem

  bkmBridge :
    NSBroadTubeSerrinLiveGapItem

canonicalNSBroadTubeSerrinLiveGapItems :
  List NSBroadTubeSerrinLiveGapItem
canonicalNSBroadTubeSerrinLiveGapItems =
  broadTubeCoarea
  ∷ serrinLift
  ∷ bkmBridge
  ∷ []

data NSBroadTubeSerrinProofObligation : Set where
  broadTubeCoareaObligation :
    NSBroadTubeSerrinProofObligation

  serrinLiftObligation :
    NSBroadTubeSerrinProofObligation

  bkmBridgeObligation :
    NSBroadTubeSerrinProofObligation

canonicalNSBroadTubeSerrinProofObligations :
  List NSBroadTubeSerrinProofObligation
canonicalNSBroadTubeSerrinProofObligations =
  broadTubeCoareaObligation
  ∷ serrinLiftObligation
  ∷ bkmBridgeObligation
  ∷ []

data NSBroadTubeSerrinPromotion : Set where

nsBroadTubeSerrinPromotionImpossibleHere :
  NSBroadTubeSerrinPromotion →
  ⊥
nsBroadTubeSerrinPromotionImpossibleHere ()

nsBroadTubeSerrinLiftGapStatement : String
nsBroadTubeSerrinLiftGapStatement =
  "Calc 8 weighted lambda2 evidence makes the strict carrier lane insufficient; the broad-tube coarea, Serrin lift, and BKM bridge gates are now represented by conditional bridge receipts, while unconditional Clay promotion remains false."

record NSBroadTubeSerrinLiftGapReceipt : Setω where
  field
    status :
      NSBroadTubeSerrinLiftGapStatus

    evidence :
      List NSBroadTubeSerrinEvidence

    evidenceIsCanonical :
      evidence ≡ canonicalNSBroadTubeSerrinEvidence

    liveGap :
      List NSBroadTubeSerrinLiveGapItem

    liveGapIsCanonical :
      liveGap ≡ canonicalNSBroadTubeSerrinLiveGapItems

    proofObligations :
      List NSBroadTubeSerrinProofObligation

    proofObligationsAreCanonical :
      proofObligations ≡ canonicalNSBroadTubeSerrinProofObligations

    calc8WeightedLambda2EvidenceFlag :
      Bool

    calc8WeightedLambda2EvidenceFlagIsTrue :
      calc8WeightedLambda2EvidenceFlag ≡ true

    strictCarrierSufficient :
      Bool

    strictCarrierSufficientIsFalse :
      strictCarrierSufficient ≡ false

    broadTubeRequired :
      Bool

    broadTubeRequiredIsTrue :
      broadTubeRequired ≡ true

    broadTubeInteriorContinuationOpenFlag :
      Bool

    broadTubeInteriorContinuationOpenFlagIsTrue :
      broadTubeInteriorContinuationOpenFlag ≡ true

    serrinLiftRequired :
      Bool

    serrinLiftRequiredIsTrue :
      serrinLiftRequired ≡ true

    bkmBridgeRequired :
      Bool

    bkmBridgeRequiredIsTrue :
      bkmBridgeRequired ≡ true

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBroadTubeSerrinLiftGapStatement

    promotionFlags :
      List NSBroadTubeSerrinPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSBroadTubeSerrinLiftGapReceipt public

canonicalNSBroadTubeSerrinLiftGapReceipt :
  NSBroadTubeSerrinLiftGapReceipt
canonicalNSBroadTubeSerrinLiftGapReceipt =
  record
    { status =
        calc8WeightedLambda2MakesStrictCarrierInsufficient
    ; evidence =
        canonicalNSBroadTubeSerrinEvidence
    ; evidenceIsCanonical =
        refl
    ; liveGap =
        canonicalNSBroadTubeSerrinLiveGapItems
    ; liveGapIsCanonical =
        refl
    ; proofObligations =
        canonicalNSBroadTubeSerrinProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; calc8WeightedLambda2EvidenceFlag =
        true
    ; calc8WeightedLambda2EvidenceFlagIsTrue =
        refl
    ; strictCarrierSufficient =
        false
    ; strictCarrierSufficientIsFalse =
        refl
    ; broadTubeRequired =
        true
    ; broadTubeRequiredIsTrue =
        refl
    ; broadTubeInteriorContinuationOpenFlag =
        true
    ; broadTubeInteriorContinuationOpenFlagIsTrue =
        refl
    ; serrinLiftRequired =
        true
    ; serrinLiftRequiredIsTrue =
        refl
    ; bkmBridgeRequired =
        true
    ; bkmBridgeRequiredIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        nsBroadTubeSerrinLiftGapStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "strict carrier insufficient"
        ∷ "broad tube required"
        ∷ "broad tube coarea conditional bridge receipt implemented"
        ∷ "serrin lift conditional bridge receipt implemented"
        ∷ "bkm bridge conditional bridge receipt implemented"
        ∷ "no clay promotion"
        ∷ []
    }
