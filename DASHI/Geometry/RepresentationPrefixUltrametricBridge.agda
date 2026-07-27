module DASHI.Geometry.RepresentationPrefixUltrametricBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; _∸_)
import Data.Vec as Vec

import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Foundations.SSPPrimeLane369Refinement as Refinement
import DASHI.Geometry.SSP369Ultrametric as U

------------------------------------------------------------------------
-- The existing 369 metric already expresses the required tree law:
-- shared origin-prefix depth bounds the remaining ultrametric distance.
------------------------------------------------------------------------

record OriginPrefixUltrametricReceipt (depth : Nat) : Set where
  field
    leftAddress : U.Address depth
    rightAddress : U.Address depth
    sharedOriginPrefix : Nat
    prefixWitness :
      U.PrefixMatch sharedOriginPrefix leftAddress rightAddress
    distanceBound :
      U.distance leftAddress rightAddress ≤ depth ∸ sharedOriginPrefix
    displayValuationReading : Radix.DisplayValuationReading
    prefixBeginsAtValuationOrigin : Bool

mkOriginPrefixUltrametricReceipt :
  ∀ {depth}
    (left right : U.Address depth)
    (shared : Nat) →
    U.PrefixMatch shared left right →
    Radix.DisplayValuationReading →
    OriginPrefixUltrametricReceipt depth
mkOriginPrefixUltrametricReceipt left right shared witness reading = record
  { leftAddress = left
  ; rightAddress = right
  ; sharedOriginPrefix = shared
  ; prefixWitness = witness
  ; distanceBound = U.prefixMatch→distanceBound witness
  ; displayValuationReading = reading
  ; prefixBeginsAtValuationOrigin = true
  }

------------------------------------------------------------------------
-- Digit adapters connect the ultrametric carrier to the refinement forest.
------------------------------------------------------------------------

ultrametricDigitToLaneDigit : U.Digit369 → Refinement.Lane369Digit
ultrametricDigitToLaneDigit U.digit3 = Refinement.digit-3
ultrametricDigitToLaneDigit U.digit6 = Refinement.digit-6
ultrametricDigitToLaneDigit U.digit9 = Refinement.digit-9

laneDigitToUltrametricDigit : Refinement.Lane369Digit → U.Digit369
laneDigitToUltrametricDigit Refinement.digit-3 = U.digit3
laneDigitToUltrametricDigit Refinement.digit-6 = U.digit6
laneDigitToUltrametricDigit Refinement.digit-9 = U.digit9

digitLaneRoundTrip :
  ∀ digit →
  laneDigitToUltrametricDigit (ultrametricDigitToLaneDigit digit) ≡ digit
digitLaneRoundTrip U.digit3 = refl
digitLaneRoundTrip U.digit6 = refl
digitLaneRoundTrip U.digit9 = refl

laneDigitUltrametricRoundTrip :
  ∀ digit →
  ultrametricDigitToLaneDigit (laneDigitToUltrametricDigit digit) ≡ digit
laneDigitUltrametricRoundTrip Refinement.digit-3 = refl
laneDigitUltrametricRoundTrip Refinement.digit-6 = refl
laneDigitUltrametricRoundTrip Refinement.digit-9 = refl

ultrametricAddressToLaneDigits :
  ∀ {depth} → U.Address depth → Vec.Vec Refinement.Lane369Digit depth
ultrametricAddressToLaneDigits Vec.[] = Vec.[]
ultrametricAddressToLaneDigits (digit Vec.∷ rest) =
  ultrametricDigitToLaneDigit digit Vec.∷ ultrametricAddressToLaneDigits rest

------------------------------------------------------------------------
-- Canonical depth-three example: two cells share the coarse 3/6 prefix and
-- differ only in the final fine digit.
------------------------------------------------------------------------

left369Address : U.Address 3
left369Address = U.digit3 Vec.∷ U.digit6 Vec.∷ U.digit9 Vec.∷ Vec.[]

right363Address : U.Address 3
right363Address = U.digit3 Vec.∷ U.digit6 Vec.∷ U.digit3 Vec.∷ Vec.[]

sharedThreeSixPrefix : U.PrefixMatch 2 left369Address right363Address
sharedThreeSixPrefix =
  U.prefix-cons U.digit3
    (U.prefix-cons U.digit6 U.prefix-zero)

canonicalThreeSixPrefixReceipt : OriginPrefixUltrametricReceipt 3
canonicalThreeSixPrefixReceipt =
  mkOriginPrefixUltrametricReceipt
    left369Address
    right363Address
    2
    sharedThreeSixPrefix
    (Radix.canonicalDecimalPAdicReading 3)

canonicalDistanceBound :
  U.distance left369Address right363Address ≤ 3 ∸ 2
canonicalDistanceBound =
  OriginPrefixUltrametricReceipt.distanceBound canonicalThreeSixPrefixReceipt

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record PrefixMetricAuthorityBoundary : Set where
  field
    textualLeftPrefixUniversallyUsed : Bool
    valuationOriginExplicit : Bool
    prefixMetricIsArchimedeanClaimed : Bool
    firstDifferenceControlsScale : Bool
    finite369MetricPromotedToAnalyticPAdicCompletion : Bool

canonicalPrefixMetricAuthorityBoundary : PrefixMetricAuthorityBoundary
canonicalPrefixMetricAuthorityBoundary = record
  { textualLeftPrefixUniversallyUsed = false
  ; valuationOriginExplicit = true
  ; prefixMetricIsArchimedeanClaimed = false
  ; firstDifferenceControlsScale = true
  ; finite369MetricPromotedToAnalyticPAdicCompletion = false
  }

prefixMetricSummary : String
prefixMetricSummary =
  "A coarse cell is a valuation-origin prefix; fine cells extend it, and the first differing block determines the finite ultrametric scale."
