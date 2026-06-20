module DASHI.Promotion.KleinHodgeDualityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ClassicalFieldObligations as Classical

------------------------------------------------------------------------
-- Klein-bottle Hodge duality boundary.
--
-- Ordinary global Hodge duality needs a metric and an orientation.
-- On a Klein bottle or any other non-orientable base, the global
-- construction is blocked.  The only candidate repair surfaces recorded
-- here are the orientable double cover (torus) lift and a twisted repair
-- layer.  No promotion bit is allowed to flip true in this module.

data HodgeBaseKind : Set where
  orientedMetricBase : HodgeBaseKind
  kleinBottleBase : HodgeBaseKind
  torusDoubleCoverBase : HodgeBaseKind
  twistedRepairLayerBase : HodgeBaseKind

data HodgeBoundaryStatus : Set where
  metricAndOrientationRequired : HodgeBoundaryStatus
  nonOrientableTopologyBlocked : HodgeBoundaryStatus
  repairCandidateOnly : HodgeBoundaryStatus
  promotionFalseBlocked : HodgeBoundaryStatus

data HodgeRepairOption : Set where
  orientableDoubleCoverLift : HodgeRepairOption
  twistedRepairLayerLift : HodgeRepairOption

data HodgeBoundaryRowKind : Set where
  ordinaryGlobalHodgeRequirementRow : HodgeBoundaryRowKind
  kleinBottleObstructionRow : HodgeBoundaryRowKind
  orientableDoubleCoverRepairRow : HodgeBoundaryRowKind
  twistedRepairLayerRow : HodgeBoundaryRowKind
  ordinaryPromotionFalseRow : HodgeBoundaryRowKind

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record HodgeBoundaryRow : Set where
  field
    rowKind : HodgeBoundaryRowKind
    baseKind : HodgeBaseKind
    status : HodgeBoundaryStatus
    targetStatement : String
    missingObligation : String
    repairOption : HodgeRepairOption
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promoted : Bool
    promotedIsFalse : promoted ≡ false

open HodgeBoundaryRow public

mkHodgeBoundaryRow :
  HodgeBoundaryRowKind →
  HodgeBaseKind →
  HodgeBoundaryStatus →
  String →
  String →
  HodgeRepairOption →
  HodgeBoundaryRow
mkHodgeBoundaryRow kind base status target missing repair =
  record
    { rowKind = kind
    ; baseKind = base
    ; status = status
    ; targetStatement = target
    ; missingObligation = missing
    ; repairOption = repair
    ; candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promoted = false
    ; promotedIsFalse = refl
    }

canonicalHodgeBoundaryRows : List HodgeBoundaryRow
canonicalHodgeBoundaryRows =
  mkHodgeBoundaryRow
    ordinaryGlobalHodgeRequirementRow
    orientedMetricBase
    metricAndOrientationRequired
    "ordinary global Hodge duality * is only meaningful with an accepted metric and orientation"
    "metric and orientation authority required for global Hodge duality"
    orientableDoubleCoverLift
  ∷ mkHodgeBoundaryRow
    kleinBottleObstructionRow
    kleinBottleBase
    nonOrientableTopologyBlocked
    "a Klein bottle has no global orientation, so ordinary global Hodge duality is blocked"
    "missing global orientation and the induced global volume-form convention"
    orientableDoubleCoverLift
  ∷ mkHodgeBoundaryRow
    orientableDoubleCoverRepairRow
    torusDoubleCoverBase
    repairCandidateOnly
    "lift the Klein bottle to its orientable double cover, recorded here as the torus repair candidate"
    "missing the orientable double-cover lift certificate that turns the non-orientable base into an orientable one"
    orientableDoubleCoverLift
  ∷ mkHodgeBoundaryRow
    twistedRepairLayerRow
    twistedRepairLayerBase
    repairCandidateOnly
    "twisted repair layer with local-system or twisted-orientation bookkeeping"
    "missing the twisted repair-layer receipt that replaces global orientation with a repaired local system"
    twistedRepairLayerLift
  ∷ mkHodgeBoundaryRow
    ordinaryPromotionFalseRow
    kleinBottleBase
    promotionFalseBlocked
    "ordinary global Hodge duality promotion remains false"
    "fail-closed promotion bit: this module never promotes the ordinary global Hodge claim"
    orientableDoubleCoverLift
  ∷ []

record KleinHodgeDualityBoundary : Set₁ where
  field
    boundaryLabel : String
    sourceHodgeObligation : Classical.MaxwellHodgeObligation
    canonicalRows : List HodgeBoundaryRow
    canonicalRowCount : Nat
    canonicalRowCountIs5 : canonicalRowCount ≡ 5
    canonicalObstruction : HodgeBoundaryRowKind
    canonicalObstructionIsKleinBottle :
      canonicalObstruction ≡ kleinBottleObstructionRow
    orientableDoubleCoverRepairAvailable : Bool
    orientableDoubleCoverRepairAvailableIsTrue :
      orientableDoubleCoverRepairAvailable ≡ true
    twistedRepairLayerAvailable : Bool
    twistedRepairLayerAvailableIsTrue :
      twistedRepairLayerAvailable ≡ true
    ordinaryGlobalHodgeDualityPromoted : Bool
    ordinaryGlobalHodgeDualityPromotedIsFalse :
      ordinaryGlobalHodgeDualityPromoted ≡ false
    kleinBottleDirectPromotion : Bool
    kleinBottleDirectPromotionIsFalse :
      kleinBottleDirectPromotion ≡ false
    orientableDoubleCoverPromotion : Bool
    orientableDoubleCoverPromotionIsFalse :
      orientableDoubleCoverPromotion ≡ false
    twistedRepairLayerPromotion : Bool
    twistedRepairLayerPromotionIsFalse :
      twistedRepairLayerPromotion ≡ false
    validationCommand : String

open KleinHodgeDualityBoundary public

canonicalKleinHodgeDualityBoundary : KleinHodgeDualityBoundary
canonicalKleinHodgeDualityBoundary = record
  { boundaryLabel =
      "Klein-bottle Hodge duality boundary"
  ; sourceHodgeObligation =
      Classical.canonicalMaxwellHodgeObligation
  ; canonicalRows =
      canonicalHodgeBoundaryRows
  ; canonicalRowCount =
      listCount canonicalHodgeBoundaryRows
  ; canonicalRowCountIs5 = refl
  ; canonicalObstruction =
      kleinBottleObstructionRow
  ; canonicalObstructionIsKleinBottle = refl
  ; orientableDoubleCoverRepairAvailable = true
  ; orientableDoubleCoverRepairAvailableIsTrue = refl
  ; twistedRepairLayerAvailable = true
  ; twistedRepairLayerAvailableIsTrue = refl
  ; ordinaryGlobalHodgeDualityPromoted = false
  ; ordinaryGlobalHodgeDualityPromotedIsFalse = refl
  ; kleinBottleDirectPromotion = false
  ; kleinBottleDirectPromotionIsFalse = refl
  ; orientableDoubleCoverPromotion = false
  ; orientableDoubleCoverPromotionIsFalse = refl
  ; twistedRepairLayerPromotion = false
  ; twistedRepairLayerPromotionIsFalse = refl
  ; validationCommand =
      "scripts/run_agda29_parallel_check.sh DASHI/Promotion/KleinHodgeDualityBoundary.agda"
  }

canonicalKleinHodgeBoundaryRowCountIs5 :
  KleinHodgeDualityBoundary.canonicalRowCount
    canonicalKleinHodgeDualityBoundary
  ≡ 5
canonicalKleinHodgeBoundaryRowCountIs5 = refl

canonicalKleinHodgeBoundaryPromotionIsFalse :
  KleinHodgeDualityBoundary.ordinaryGlobalHodgeDualityPromoted
    canonicalKleinHodgeDualityBoundary
  ≡ false
canonicalKleinHodgeBoundaryPromotionIsFalse = refl

canonicalKleinBottleDirectPromotionIsFalse :
  KleinHodgeDualityBoundary.kleinBottleDirectPromotion
    canonicalKleinHodgeDualityBoundary
  ≡ false
canonicalKleinBottleDirectPromotionIsFalse = refl

canonicalOrientableDoubleCoverPromotionIsFalse :
  KleinHodgeDualityBoundary.orientableDoubleCoverPromotion
    canonicalKleinHodgeDualityBoundary
  ≡ false
canonicalOrientableDoubleCoverPromotionIsFalse = refl

canonicalTwistedRepairLayerPromotionIsFalse :
  KleinHodgeDualityBoundary.twistedRepairLayerPromotion
    canonicalKleinHodgeDualityBoundary
  ≡ false
canonicalTwistedRepairLayerPromotionIsFalse = refl
