module DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact where

------------------------------------------------------------------------
-- CONCRETE PINNED BISHOP INSTANCE OF THE MINIMAL RH HEIGHT CARRIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Analysis.RiemannLocatedHeightCarrierExact as Height
import DASHI.Analysis.RiemannBishopPlattTrudgianLocatedHeightExact as PT

bishopLocatedHeightCarrier : Height.LocatedHeightCarrier
bishopLocatedHeightCarrier = record
  { Height.Carrier = Bishop.ℝ
  ; Height.abs = Bishop.∣_∣
  ; Height._<_ = Bishop._<_
  ; Height.highStart = PT.candidateHalfBishop
  ; Height.publishedHeight = PT.publishedVerifiedHeightBishop
  ; Height.highStartBelowPublishedHeight =
      PT.candidateHalfBelowPublishedHeightBishop
  ; Height.locatedBetweenThresholds =
      λ value →
        BishopLaws.fast-corollary-2-17
          value
          PT.candidateHalfBishop
          PT.publishedVerifiedHeightBishop
          PT.candidateHalfBelowPublishedHeightBishop
  }

record BishopLocatedHeightCarrierBoundary : Set where
  constructor bishop-located-height-carrier-boundary
  field
    concreteBishopCarrierInhabited : Bool
    exactPTThresholdsUsed : Bool
    locatedSplitKernelTheoremUsed : Bool
    completeRealCapabilityBundleRequired : Bool
    excludedMiddleUsed : Bool
    rhDerivedHere : Bool

open BishopLocatedHeightCarrierBoundary public

canonicalBishopLocatedHeightCarrierBoundary :
  BishopLocatedHeightCarrierBoundary
canonicalBishopLocatedHeightCarrierBoundary =
  bishop-located-height-carrier-boundary
    true true true false false false
