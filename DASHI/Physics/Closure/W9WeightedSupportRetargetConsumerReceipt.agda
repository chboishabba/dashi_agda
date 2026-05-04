module DASHI.Physics.Closure.W9WeightedSupportRetargetConsumerReceipt where

-- Planck/W9: narrow retarget consumer for the existing weighted support
-- bound.  This inhabits the current RetargetConsumerInterface and acceptance
-- receipt for the canonical pressure-compatible retarget receipt.  It does
-- not construct a CancellationPressureLyapunovBridge, an admissible quadratic,
-- a dim-15 pressure witness, or CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)

import DASHI.Arithmetic.MaxPressure as Max
import DASHI.Arithmetic.WeightedPressure as Weighted
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f

weightedSupportRetargetAcceptance :
  W9.PressureCompatibleTargetWithQcoreBoundaryReceipt →
  Set
weightedSupportRetargetAcceptance _ =
  ∀ x y →
    Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

weightedSupportRetargetConsumer :
  W9f.RetargetConsumerInterface
weightedSupportRetargetConsumer =
  record
    { acceptsRetargetReceipt =
        weightedSupportRetargetAcceptance
    ; acceptanceIsNonPromoting =
        W9f.noCancellationPressureCompatibilityPromotion
    }

weightedSupportRetargetAcceptanceReceipt :
  W9f.CancellationPressureRetargetConsumerAcceptanceReceipt
    weightedSupportRetargetConsumer
    W9.canonicalPairPressureRetargetReceipt
weightedSupportRetargetAcceptanceReceipt =
  record
    { acceptsSelectedPressureCompatibleRoute =
        refl
    ; acceptsPressureBridgeMatchedBoundary =
        refl
    ; preservesNonQcoreBoundary =
        refl
    ; acknowledgesRetargetNonPromotion =
        refl
    ; downstreamConsumerAcceptance =
        Max.weightedMaxPressure≤weightedSupport
    ; downstreamAcceptanceBoundary =
        refl
    }

weightedSupportRetargetObligation :
  W9f.CanonicalPairPressureRetargetConsumerObligation
weightedSupportRetargetObligation =
  W9f.canonicalPairPressureRetargetConsumerObligation
    weightedSupportRetargetConsumer

data W9WeightedSupportRetargetScope : Set where
  retargetConsumerAcceptedOnly :
    W9WeightedSupportRetargetScope

record WeightedSupportRetargetConsumerReceipt : Setω where
  field
    weightedSupportBound :
      ∀ x y →
        Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

    consumer :
      W9f.RetargetConsumerInterface

    acceptance :
      W9f.CancellationPressureRetargetConsumerAcceptanceReceipt
        consumer
        W9.canonicalPairPressureRetargetReceipt

    canonicalObligation :
      W9f.CanonicalPairPressureRetargetConsumerObligation

    selectedRouteIsRetarget :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.selectedNextRoute
        W9.canonicalPairPressureRetargetReceipt
      ≡
      W9.supplyPressureCompatibleTargetWithQcoreBoundary

    nonPromotionBoundary :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.nonPromotionBoundary
        W9.canonicalPairPressureRetargetReceipt
      ≡
      W9.retargetMustNotClaimCanonicalQcore

    receiptScope :
      W9WeightedSupportRetargetScope

    stillNotConstructed :
      List String

canonicalWeightedSupportRetargetConsumerReceipt :
  WeightedSupportRetargetConsumerReceipt
canonicalWeightedSupportRetargetConsumerReceipt =
  record
    { weightedSupportBound =
        Max.weightedMaxPressure≤weightedSupport
    ; consumer =
        weightedSupportRetargetConsumer
    ; acceptance =
        weightedSupportRetargetAcceptanceReceipt
    ; canonicalObligation =
        weightedSupportRetargetObligation
    ; selectedRouteIsRetarget =
        refl
    ; nonPromotionBoundary =
        refl
    ; receiptScope =
        retargetConsumerAcceptedOnly
    ; stillNotConstructed =
        "No CancellationPressureLyapunovBridge is constructed"
        ∷ "No dim-15 pressure witness is constructed"
        ∷ "No admissible quadratic or canonical Qcore promotion is constructed"
        ∷ "No CancellationPressureCompatibility or W9 kill receipt is constructed"
        ∷ []
    }

currentW9WeightedSupportRetargetScope :
  W9WeightedSupportRetargetScope
currentW9WeightedSupportRetargetScope =
  WeightedSupportRetargetConsumerReceipt.receiptScope
    canonicalWeightedSupportRetargetConsumerReceipt
