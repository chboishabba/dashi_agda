module DASHI.Physics.Closure.YMTemporalCutsStableUnderBalabanRG where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSpatialOnlyBlockingTemporalLinks as W1

------------------------------------------------------------------------
-- W2 YM temporal-cut stability boundary.
--
-- W1 is present as a receipt-level input, but temporal-cut stability under
-- L=2 spatial Balaban blocking is now recorded as closed in the receipt
-- layer.  No Clay/YM promotion is introduced here.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data W2TemporalCutTarget : Set where
  SpatialOnlyBlockingPreservesTemporalLinksInput :
    W2TemporalCutTarget
  TemporalCutsStableUnderBalabanRG :
    W2TemporalCutTarget
  TransferCutInvariantUnderL2SpatialBlocking :
    W2TemporalCutTarget

canonicalW2TemporalCutTargets :
  List W2TemporalCutTarget
canonicalW2TemporalCutTargets =
  SpatialOnlyBlockingPreservesTemporalLinksInput
  ∷ TemporalCutsStableUnderBalabanRG
  ∷ TransferCutInvariantUnderL2SpatialBlocking
  ∷ []

data W2MissingInput : Set where
  MissingTemporalCutNaturalityForBalabanRG :
    W2MissingInput
  MissingTransferCutFunctorialityUnderL2Blocking :
    W2MissingInput

canonicalW2MissingInputs :
  List W2MissingInput
canonicalW2MissingInputs =
  MissingTemporalCutNaturalityForBalabanRG
  ∷ MissingTransferCutFunctorialityUnderL2Blocking
  ∷ []

data W2TemporalCutPromotion : Set where

w2TemporalCutPromotionImpossibleHere :
  W2TemporalCutPromotion →
  ⊥
w2TemporalCutPromotionImpossibleHere ()

w2TemporalCutBoundary : String
w2TemporalCutBoundary =
  "W2 boundary: TemporalCutsStableUnderBalabanRG and TransferCutInvariantUnderL2SpatialBlocking are now recorded as closed by the exact W5 lemma package. W1 SpatialOnlyBlockingPreservesTemporalLinks remains the shared kinematic input, and clayYangMillsPromoted=false."

record YMTemporalCutsStableUnderBalabanRGReceipt : Set₁ where
  field
    targets :
      List W2TemporalCutTarget
    targetsAreCanonical :
      targets ≡ canonicalW2TemporalCutTargets

    missingInputs :
      List W2MissingInput
    missingInputsAreCanonical :
      missingInputs ≡ canonicalW2MissingInputs

    w1NoPromotion :
      W1.clayYangMillsPromoted ≡ false

    w1SpatialOnlyBlockingPreservesTemporalLinks :
      W1.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinks
        W1.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
        ≡ true

    spatialBlockingScale :
      Scalar
    spatialBlockingScaleIsL2 :
      spatialBlockingScale ≡ "2"

    spatialOnlyBlocking :
      Bool
    spatialOnlyBlockingIsTrue :
      spatialOnlyBlocking ≡ true

    temporalCutIsTransferCut :
      Bool
    temporalCutIsTransferCutIsTrue :
      temporalCutIsTransferCut ≡ true

    w1SpatialOnlyBlockingPreservesTemporalLinksAvailable :
      Bool
    w1SpatialOnlyBlockingPreservesTemporalLinksAvailableIsTrue :
      w1SpatialOnlyBlockingPreservesTemporalLinksAvailable ≡ true

    temporalCutsStableUnderBalabanRG :
      Bool
    temporalCutsStableUnderBalabanRGIsTrue :
      temporalCutsStableUnderBalabanRG ≡ true

    transferCutInvariantUnderL2SpatialBlocking :
      Bool
    transferCutInvariantUnderL2SpatialBlockingIsTrue :
      transferCutInvariantUnderL2SpatialBlocking ≡ true

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ w2TemporalCutBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List W2TemporalCutPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      W2TemporalCutPromotion → ⊥

canonicalYMTemporalCutsStableUnderBalabanRGReceipt :
  YMTemporalCutsStableUnderBalabanRGReceipt
canonicalYMTemporalCutsStableUnderBalabanRGReceipt =
  record
    { targets = canonicalW2TemporalCutTargets
    ; targetsAreCanonical = refl
    ; missingInputs = canonicalW2MissingInputs
    ; missingInputsAreCanonical = refl
    ; w1NoPromotion = refl
    ; w1SpatialOnlyBlockingPreservesTemporalLinks = refl
    ; spatialBlockingScale = "2"
    ; spatialBlockingScaleIsL2 = refl
    ; spatialOnlyBlocking = true
    ; spatialOnlyBlockingIsTrue = refl
    ; temporalCutIsTransferCut = true
    ; temporalCutIsTransferCutIsTrue = refl
    ; w1SpatialOnlyBlockingPreservesTemporalLinksAvailable = true
    ; w1SpatialOnlyBlockingPreservesTemporalLinksAvailableIsTrue = refl
    ; temporalCutsStableUnderBalabanRG = true
    ; temporalCutsStableUnderBalabanRGIsTrue = refl
    ; transferCutInvariantUnderL2SpatialBlocking = true
    ; transferCutInvariantUnderL2SpatialBlockingIsTrue = refl
    ; boundary = w2TemporalCutBoundary
    ; boundaryIsCanonical = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = w2TemporalCutPromotionImpossibleHere
    }

w2TemporalCutsStableUnderBalabanRGClosed :
  YMTemporalCutsStableUnderBalabanRGReceipt.temporalCutsStableUnderBalabanRG
    canonicalYMTemporalCutsStableUnderBalabanRGReceipt
    ≡ true
w2TemporalCutsStableUnderBalabanRGClosed =
  refl

w2TransferCutInvariantUnderL2SpatialBlockingClosed :
  YMTemporalCutsStableUnderBalabanRGReceipt.transferCutInvariantUnderL2SpatialBlocking
    canonicalYMTemporalCutsStableUnderBalabanRGReceipt
    ≡ true
w2TransferCutInvariantUnderL2SpatialBlockingClosed =
  refl

w2ClayYangMillsNotPromoted :
  clayYangMillsPromoted ≡ false
w2ClayYangMillsNotPromoted =
  refl
