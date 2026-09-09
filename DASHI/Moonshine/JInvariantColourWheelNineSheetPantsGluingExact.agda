module DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact where

------------------------------------------------------------------------
-- COLOUR WHEEL / 9-SHEET / TERNARY PANTS GLUING
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; tri-low ; tri-mid ; tri-high
  )

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact as Wheel
import DASHI.Reasoning.TernaryPantsSynthesisS3BridgeExact as PantsS3
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

triTruthToKernel : TriTruth → Triadic.KernelTrit
triTruthToKernel tri-low = Triadic.negativeTrit
triTruthToKernel tri-mid = Triadic.zeroTrit
triTruthToKernel tri-high = Triadic.positiveTrit

kernelToTriTruth : Triadic.KernelTrit → TriTruth
kernelToTriTruth Triadic.negativeTrit = tri-low
kernelToTriTruth Triadic.zeroTrit = tri-mid
kernelToTriTruth Triadic.positiveTrit = tri-high

kernelTriRoundTrip :
  (t : Triadic.KernelTrit) → triTruthToKernel (kernelToTriTruth t) ≡ t
kernelTriRoundTrip Triadic.negativeTrit = refl
kernelTriRoundTrip Triadic.zeroTrit = refl
kernelTriRoundTrip Triadic.positiveTrit = refl

triKernelRoundTrip :
  (t : TriTruth) → kernelToTriTruth (triTruthToKernel t) ≡ t
triKernelRoundTrip tri-low = refl
triKernelRoundTrip tri-mid = refl
triKernelRoundTrip tri-high = refl

polarityToKernel : Mobius.OrientationPolarity → Triadic.KernelTrit
polarityToKernel Mobius.positive = Triadic.positiveTrit
polarityToKernel Mobius.negative = Triadic.negativeTrit

kernelToSSP : Triadic.KernelTrit → SSP.SSPTrit
kernelToSSP Triadic.negativeTrit = SSP.sspNegOne
kernelToSSP Triadic.zeroTrit = SSP.sspZero
kernelToSSP Triadic.positiveTrit = SSP.sspPosOne

sspToKernel : SSP.SSPTrit → Triadic.KernelTrit
sspToKernel SSP.sspNegOne = Triadic.negativeTrit
sspToKernel SSP.sspZero = Triadic.zeroTrit
sspToKernel SSP.sspPosOne = Triadic.positiveTrit

sspKernelRoundTrip :
  (t : SSP.SSPTrit) → kernelToSSP (sspToKernel t) ≡ t
sspKernelRoundTrip SSP.sspNegOne = refl
sspKernelRoundTrip SSP.sspZero = refl
sspKernelRoundTrip SSP.sspPosOne = refl

kernelSSPRoundTrip :
  (t : Triadic.KernelTrit) → sspToKernel (kernelToSSP t) ≡ t
kernelSSPRoundTrip Triadic.negativeTrit = refl
kernelSSPRoundTrip Triadic.zeroTrit = refl
kernelSSPRoundTrip Triadic.positiveTrit = refl

kernelToSlot : Triadic.KernelTrit → Pants.BranchSlot
kernelToSlot t = PantsS3.truthToSlot (kernelToTriTruth t)

slotToKernel : Pants.BranchSlot → Triadic.KernelTrit
slotToKernel s = triTruthToKernel (PantsS3.slotToTruth s)

kernelSlotRoundTrip :
  (t : Triadic.KernelTrit) → slotToKernel (kernelToSlot t) ≡ t
kernelSlotRoundTrip Triadic.negativeTrit = refl
kernelSlotRoundTrip Triadic.zeroTrit = refl
kernelSlotRoundTrip Triadic.positiveTrit = refl

slotKernelRoundTrip :
  (s : Pants.BranchSlot) → kernelToSlot (slotToKernel s) ≡ s
slotKernelRoundTrip Pants.slot3 = refl
slotKernelRoundTrip Pants.slot6 = refl
slotKernelRoundTrip Pants.slot9 = refl

------------------------------------------------------------------------
-- Six-state wheel = strict-nonzero seam subset of the nine-sheet.
------------------------------------------------------------------------

record StrictWheelSheet : Set where
  constructor strict-wheel-sheet
  field
    phase : Triadic.KernelTrit
    polarity : Mobius.OrientationPolarity

open StrictWheelSheet public

hexToStrictSheet : HexTruth → StrictWheelSheet
hexToStrictSheet h =
  strict-wheel-sheet
    (triTruthToKernel (Mobius.hexTriadicPhase h))
    (Mobius.hexOrientationPolarity h)

strictSheetToHex : StrictWheelSheet → HexTruth
strictSheetToHex (strict-wheel-sheet p o) =
  Wheel.curlSix (Wheel.uncurledSix (kernelToTriTruth p) o)

hexStrictRoundTrip : (h : HexTruth) → strictSheetToHex (hexToStrictSheet h) ≡ h
hexStrictRoundTrip hex-0 = refl
hexStrictRoundTrip hex-1 = refl
hexStrictRoundTrip hex-2 = refl
hexStrictRoundTrip hex-3 = refl
hexStrictRoundTrip hex-4 = refl
hexStrictRoundTrip hex-5 = refl

strictHexRoundTrip : (s : StrictWheelSheet) → hexToStrictSheet (strictSheetToHex s) ≡ s
strictHexRoundTrip (strict-wheel-sheet Triadic.negativeTrit Mobius.positive) = refl
strictHexRoundTrip (strict-wheel-sheet Triadic.zeroTrit Mobius.positive) = refl
strictHexRoundTrip (strict-wheel-sheet Triadic.positiveTrit Mobius.positive) = refl
strictHexRoundTrip (strict-wheel-sheet Triadic.negativeTrit Mobius.negative) = refl
strictHexRoundTrip (strict-wheel-sheet Triadic.zeroTrit Mobius.negative) = refl
strictHexRoundTrip (strict-wheel-sheet Triadic.positiveTrit Mobius.negative) = refl

strictSheetToNine : StrictWheelSheet → Triadic.NineSheet
strictSheetToNine (strict-wheel-sheet p Mobius.positive) = p , Triadic.positiveTrit
strictSheetToNine (strict-wheel-sheet p Mobius.negative) = p , Triadic.negativeTrit

colourWheelNine : HexTruth → Triadic.NineSheet
colourWheelNine h = strictSheetToNine (hexToStrictSheet h)

neutralSeamSheet : Triadic.KernelTrit → Triadic.NineSheet
neutralSeamSheet p = p , Triadic.zeroTrit

data NonzeroSeamCoordinate : Triadic.KernelTrit → Set where
  negativeSeam : NonzeroSeamCoordinate Triadic.negativeTrit
  positiveSeam : NonzeroSeamCoordinate Triadic.positiveTrit

colourWheelAlwaysHasNonzeroSeam :
  (h : HexTruth) → NonzeroSeamCoordinate (proj₂ (colourWheelNine h))
colourWheelAlwaysHasNonzeroSeam hex-0 = positiveSeam
colourWheelAlwaysHasNonzeroSeam hex-1 = positiveSeam
colourWheelAlwaysHasNonzeroSeam hex-2 = positiveSeam
colourWheelAlwaysHasNonzeroSeam hex-3 = negativeSeam
colourWheelAlwaysHasNonzeroSeam hex-4 = negativeSeam
colourWheelAlwaysHasNonzeroSeam hex-5 = negativeSeam

flipNineSeam : Triadic.NineSheet → Triadic.NineSheet
flipNineSeam (p , s) = p , Triadic.negateTrit s

mobiusWheelBecomesNineSeamFlip :
  (h : HexTruth) →
  colourWheelNine (Mobius.mobiusTransport h) ≡ flipNineSeam (colourWheelNine h)
mobiusWheelBecomesNineSeamFlip hex-0 = refl
mobiusWheelBecomesNineSeamFlip hex-1 = refl
mobiusWheelBecomesNineSeamFlip hex-2 = refl
mobiusWheelBecomesNineSeamFlip hex-3 = refl
mobiusWheelBecomesNineSeamFlip hex-4 = refl
mobiusWheelBecomesNineSeamFlip hex-5 = refl

neutralSeamFixedByFlip :
  (p : Triadic.KernelTrit) → flipNineSeam (neutralSeamSheet p) ≡ neutralSeamSheet p
neutralSeamFixedByFlip p = refl

------------------------------------------------------------------------
-- Nine-sheet = depth-two pants path.
------------------------------------------------------------------------

nineToPants2 : Triadic.NineSheet → Frontier.PantsPath 2
nineToPants2 (a , b) = kernelToSlot a vcons kernelToSlot b vcons vnil

pants2ToNine : Frontier.PantsPath 2 → Triadic.NineSheet
pants2ToNine (a vcons b vcons vnil) = slotToKernel a , slotToKernel b

ninePantsRoundTrip :
  (sheet : Triadic.NineSheet) → pants2ToNine (nineToPants2 sheet) ≡ sheet
ninePantsRoundTrip (a , b)
  rewrite kernelSlotRoundTrip a | kernelSlotRoundTrip b = refl

pantsNineRoundTrip :
  (path : Frontier.PantsPath 2) → nineToPants2 (pants2ToNine path) ≡ path
pantsNineRoundTrip (a vcons b vcons vnil)
  rewrite slotKernelRoundTrip a | slotKernelRoundTrip b = refl

------------------------------------------------------------------------
-- Ternary 27-point = depth-three pants path.
------------------------------------------------------------------------

voxel27ToPants3 : Fabric.Ternary27Point → Frontier.PantsPath 3
voxel27ToPants3 (Fabric.ternary27Point x y z) =
  kernelToSlot (sspToKernel x)
  vcons kernelToSlot (sspToKernel y)
  vcons kernelToSlot (sspToKernel z)
  vcons vnil

pants3ToVoxel27 : Frontier.PantsPath 3 → Fabric.Ternary27Point
pants3ToVoxel27 (a vcons b vcons c vcons vnil) =
  Fabric.ternary27Point
    (kernelToSSP (slotToKernel a))
    (kernelToSSP (slotToKernel b))
    (kernelToSSP (slotToKernel c))

voxelPantsRoundTrip :
  (v : Fabric.Ternary27Point) → pants3ToVoxel27 (voxel27ToPants3 v) ≡ v
voxelPantsRoundTrip (Fabric.ternary27Point x y z)
  rewrite kernelSlotRoundTrip (sspToKernel x)
        | kernelSlotRoundTrip (sspToKernel y)
        | kernelSlotRoundTrip (sspToKernel z)
        | sspKernelRoundTrip x
        | sspKernelRoundTrip y
        | sspKernelRoundTrip z = refl

pantsVoxelRoundTrip :
  (path : Frontier.PantsPath 3) → voxel27ToPants3 (pants3ToVoxel27 path) ≡ path
pantsVoxelRoundTrip (a vcons b vcons c vcons vnil)
  rewrite kernelSSPRoundTrip (slotToKernel a)
        | kernelSSPRoundTrip (slotToKernel b)
        | kernelSSPRoundTrip (slotToKernel c)
        | slotKernelRoundTrip a
        | slotKernelRoundTrip b
        | slotKernelRoundTrip c = refl

record ColourWheelNinePantsBoundary : Set where
  constructor colour-wheel-nine-pants-boundary
  field
    colourWheelSixEmbedsInNineSheet : Bool
    neutralSeamCompletesSixToNine : Bool
    nineSheetIsDepthTwoPantsPath : Bool
    twentySevenIsDepthThreePantsPath : Bool
    mobiusActsAsSecondCoordinateSeamFlip : Bool
    zeroSeamIsAnalyticVisualWaist : Bool
    finitePantsPathIsSmoothPantsSurface : Bool

canonicalColourWheelNinePantsBoundary : ColourWheelNinePantsBoundary
canonicalColourWheelNinePantsBoundary =
  colour-wheel-nine-pants-boundary true true true true true false false
