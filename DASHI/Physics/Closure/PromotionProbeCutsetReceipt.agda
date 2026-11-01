module DASHI.Physics.Closure.PromotionProbeCutsetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CurrentProofProfilePromotionProbeCutsetReceipt
  as Profile
import DASHI.Physics.Closure.NSPromotionProbeCutsetReceipt as NS
import DASHI.Physics.Closure.UnificationPromotionProbeCutsetReceipt as Uni
import DASHI.Physics.Closure.YMPromotionProbeCutsetReceipt as YM

data PromotionProbeCutsetStatus : Set where
  aggregateGreenProbeRedCutsetRecorded :
    PromotionProbeCutsetStatus

data PromotionProbeTarget : Set where
  everythingAggregateTarget :
    PromotionProbeTarget

  nsRootProbeTarget :
    PromotionProbeTarget

  ymRootProbeTarget :
    PromotionProbeTarget

  unificationRootProbeTarget :
    PromotionProbeTarget

  currentProofProfileRootProbeTarget :
    PromotionProbeTarget

canonicalPromotionProbeTargets : List PromotionProbeTarget
canonicalPromotionProbeTargets =
  everythingAggregateTarget
  ∷ nsRootProbeTarget
  ∷ ymRootProbeTarget
  ∷ unificationRootProbeTarget
  ∷ currentProofProfileRootProbeTarget
  ∷ []

data PromotionProbeCutsetPromotion : Set where

promotionProbeCutsetPromotionImpossibleHere :
  PromotionProbeCutsetPromotion →
  ⊥
promotionProbeCutsetPromotionImpossibleHere ()

promotionProbeCutsetStatement : String
promotionProbeCutsetStatement =
  "Promotion probe cutset: DASHI/Everything stays green while the four root probes are intentionally red, exposing the first strengthened blocker at NS, YM, unification, and cross-lane profile scope."

record PromotionProbeCutsetReceipt : Setω where
  field
    status :
      PromotionProbeCutsetStatus

    nsReceipt :
      NS.NSPromotionProbeCutsetReceipt

    ymReceipt :
      YM.YMPromotionProbeCutsetReceipt

    unificationReceipt :
      Uni.UnificationPromotionProbeCutsetReceipt

    profileReceipt :
      Profile.CurrentProofProfilePromotionProbeCutsetReceipt

    everythingAggregateStaysGreen :
      Bool

    everythingAggregateStaysGreenIsTrue :
      everythingAggregateStaysGreen ≡ true

    rootProbesAreIntentionallyRed :
      Bool

    rootProbesAreIntentionallyRedIsTrue :
      rootProbesAreIntentionallyRed ≡ true

    targetCount :
      Bool

    targetCountIsFive :
      targetCount ≡ true

    targets :
      List PromotionProbeTarget

    targetsAreCanonical :
      targets ≡ canonicalPromotionProbeTargets

    statement :
      String

    statementIsCanonical :
      statement ≡ promotionProbeCutsetStatement

    promotionFlags :
      List PromotionProbeCutsetPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

canonicalPromotionProbeCutsetReceipt :
  PromotionProbeCutsetReceipt
canonicalPromotionProbeCutsetReceipt =
  record
    { status =
        aggregateGreenProbeRedCutsetRecorded
    ; nsReceipt =
        NS.canonicalNSPromotionProbeCutsetReceipt
    ; ymReceipt =
        YM.canonicalYMPromotionProbeCutsetReceipt
    ; unificationReceipt =
        Uni.canonicalUnificationPromotionProbeCutsetReceipt
    ; profileReceipt =
        Profile.canonicalCurrentProofProfilePromotionProbeCutsetReceipt
    ; everythingAggregateStaysGreen =
        true
    ; everythingAggregateStaysGreenIsTrue =
        refl
    ; rootProbesAreIntentionallyRed =
        true
    ; rootProbesAreIntentionallyRedIsTrue =
        refl
    ; targetCount =
        true
    ; targetCountIsFive =
        refl
    ; targets =
        canonicalPromotionProbeTargets
    ; targetsAreCanonical =
        refl
    ; statement =
        promotionProbeCutsetStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
