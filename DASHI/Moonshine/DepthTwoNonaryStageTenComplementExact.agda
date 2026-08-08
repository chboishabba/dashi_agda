module DASHI.Moonshine.DepthTwoNonaryStageTenComplementExact where

open import DASHI.Core.Prelude

import DASHI.Biology.StageSymmetrySSP15BridgeExact as SSP
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- The arithmetic candidate is
--
--     b^2 = (b + 1) + (b^2 - b - 1).
--
-- At b=9 this gives 81 = 10 + 71.  A certificate records the carrier sizes
-- and the exact partition equation without pretending that cardinal arithmetic
-- constructs an invariant Monster submodule.
------------------------------------------------------------------------

record CrossScaleComplementCertificate : Set where
  constructor cross-scale-complement-certificate
  field
    base : Nat
    depthTwoTotal : Nat
    firstCrossScaleBundle : Nat
    complement : Nat
    totalIsBaseSquared : depthTwoTotal ≡ base * base
    bundleIsBasePlusOne : firstCrossScaleBundle ≡ base + 1
    partitionExact : firstCrossScaleBundle + complement ≡ depthTwoTotal

open CrossScaleComplementCertificate public

nonaryStageTenComplement : CrossScaleComplementCertificate
nonaryStageTenComplement =
  cross-scale-complement-certificate
    9 81 10 71 refl refl refl

nonaryDepthTwoIsTenPlusSeventyOne : 10 + 71 ≡ 81
nonaryDepthTwoIsTenPlusSeventyOne =
  partitionExact nonaryStageTenComplement

seventyOneIsNineSquaredMinusBundleDivisionFree :
  10 + 71 ≡ 9 * 9
seventyOneIsNineSquaredMinusBundleDivisionFree = refl

seventyOneMatchesExistingOggLane :
  SSP.oggPrimeLaneValue Lane.p71 ≡ 71
seventyOneMatchesExistingOggLane = SSP.seventyOneIsExistingOggLane

record InvariantComplementWitness : Set₁ where
  field
    Carrier81 Carrier10 Carrier71 : Set
    include10 : Carrier10 → Carrier81
    include71 : Carrier71 → Carrier81
    disjointImages : Set
    exhaustiveImages : Set
    Action : Set
    actionPreserves10 : Set
    actionPreserves71 : Set

record DepthTwoComplementBoundary : Set where
  constructor depth-two-complement-boundary
  field
    arithmeticComplementConstructed : Bool
    arithmeticComplementConstructedIsTrue :
      arithmeticComplementConstructed ≡ true
    existingP71LaneMatched : Bool
    existingP71LaneMatchedIsTrue : existingP71LaneMatched ≡ true
    invariantCarrierComplementConstructed : Bool
    invariantCarrierComplementConstructedIsFalse :
      invariantCarrierComplementConstructed ≡ false
    moduleExactSequenceConstructed : Bool
    moduleExactSequenceConstructedIsFalse :
      moduleExactSequenceConstructed ≡ false

canonicalDepthTwoComplementBoundary : DepthTwoComplementBoundary
canonicalDepthTwoComplementBoundary =
  depth-two-complement-boundary
    true refl true refl false refl false refl
