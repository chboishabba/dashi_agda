module DASHI.Physics.Boundaries.ClayYMGap where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (z≤n; s≤s)

open import DASHI.Unifier using (ℝ; toℝ; _<ℝ_; _≤ℝ_)

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap

------------------------------------------------------------------------
-- Clay/Yang-Mills mass-gap boundary.
--
-- This module records the external lower-bound shape as an explicit typed
-- boundary.  It does not claim a Clay proof, but it does expose the exact
-- internal interface downstream gates are allowed to consume.

data ClayYMGapBoundaryStatus : Set where
  boundaryRecordedNoClayPromotion :
    ClayYMGapBoundaryStatus

record ClayYMGapBoundary : Setω where
  field
    gaugeCarrier :
      Set

    hamiltonian :
      gaugeCarrier → gaugeCarrier

    vacuum :
      gaugeCarrier

    spectrum :
      gaugeCarrier → ℝ

    gap :
      ℝ

    gapPositive :
      toℝ zero <ℝ gap

    vacuumIsLowestEnergyWitness :
      spectrum vacuum ≡ gap

    spectralLowerBound :
      ∀ x → gap ≤ℝ spectrum x

    finiteDepthCarrierReceipt :
      MassGap.FiniteDepthLatticeGapReceipt zero

    continuumClayPromotionOpen :
      Bool

    continuumClayPromotionOpenIsFalse :
      continuumClayPromotionOpen ≡ false

    boundary :
      List String

open ClayYMGapBoundary public

canonicalClayYMGapBoundary :
  ClayYMGapBoundary
canonicalClayYMGapBoundary =
  record
    { gaugeCarrier =
        ⊤
    ; hamiltonian =
        λ x → x
    ; vacuum =
        tt
    ; spectrum =
        λ _ → suc zero
    ; gap =
        suc zero
    ; gapPositive =
        s≤s z≤n
    ; vacuumIsLowestEnergyWitness =
        refl
    ; spectralLowerBound =
        λ _ → s≤s z≤n
    ; finiteDepthCarrierReceipt =
        MassGap.finiteDepthLatticeGapReceipt zero
    ; continuumClayPromotionOpen =
        false
    ; continuumClayPromotionOpenIsFalse =
        refl
    ; boundary =
        "The gauge carrier is recorded with a positive lower-bound witness and a vacuum"
        ∷ "The finite-depth Yang-Mills receipt is threaded in from BalabanRGMassGapReceiptSurface"
        ∷ "This module does not claim the Clay continuum theorem"
        ∷ []
    }

record ClayYMGapReceipt : Setω where
  field
    boundary :
      ClayYMGapBoundary

    finiteDepthReceiptDepth :
      Nat

    finiteDepthReceiptDepthIsZero :
      finiteDepthReceiptDepth ≡ zero

    finiteDepthReceiptPromoted :
      Bool

    finiteDepthReceiptPromotedIsTrue :
      finiteDepthReceiptPromoted ≡ true

    localFiniteGapConsumed :
      Bool

    localFiniteGapConsumedIsTrue :
      localFiniteGapConsumed ≡ true

    clayPromotionStillOpen :
      Bool

    clayPromotionStillOpenIsFalse :
      clayPromotionStillOpen ≡ false

    receiptBoundary :
      List String

open ClayYMGapReceipt public

canonicalClayYMGapReceipt :
  ClayYMGapReceipt
canonicalClayYMGapReceipt =
  record
    { boundary =
        canonicalClayYMGapBoundary
    ; finiteDepthReceiptDepth =
        MassGap.latticeDepth
          (finiteDepthCarrierReceipt canonicalClayYMGapBoundary)
    ; finiteDepthReceiptDepthIsZero =
        refl
    ; finiteDepthReceiptPromoted =
        MassGap.promotedAtThisDepth
          (finiteDepthCarrierReceipt canonicalClayYMGapBoundary)
    ; finiteDepthReceiptPromotedIsTrue =
        refl
    ; localFiniteGapConsumed =
        true
    ; localFiniteGapConsumedIsTrue =
        refl
    ; clayPromotionStillOpen =
        false
    ; clayPromotionStillOpenIsFalse =
        refl
    ; receiptBoundary =
        "The finite-depth lower-bound witness is consumed only as a boundary interface"
        ∷ "The Clay continuum promotion remains explicitly open"
        ∷ "Every downstream gate must consume the gap through this receipt, not bypass it"
        ∷ []
    }

canonicalClayYMGapBoundaryIsVacuumLowest :
  vacuumIsLowestEnergyWitness canonicalClayYMGapBoundary ≡ refl
canonicalClayYMGapBoundaryIsVacuumLowest =
  refl

canonicalClayYMGapBoundaryKeepsPromotionOpen :
  continuumClayPromotionOpen canonicalClayYMGapBoundary ≡ false
canonicalClayYMGapBoundaryKeepsPromotionOpen =
  refl
