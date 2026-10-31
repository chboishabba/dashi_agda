{-# OPTIONS --safe #-}
module DASHI.Moonshine.Base369OrientedNineSheetInto27BidiExact where

-- Concrete 9 × 2 = 18 oriented-sheet embedding into the 27-point cube.
-- The image occupies the two nonneutral z-faces. The remaining neutral
-- z-plane has nine points. This is an injective restricted face transport,
-- NOT a claimed equivalence of the 18- and 27-element carriers.
-- Reuses canonical NineSheet, orientation and SSP/Kernel conversion.

open import DASHI.Core.Prelude
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Wheel

OrientedNineSheet : Set
OrientedNineSheet = Triadic.NineSheet × Mobius.OrientationPolarity

orientTrit : Mobius.OrientationPolarity → SSP.SSPTrit
orientTrit Mobius.positive = SSP.sspPosOne
orientTrit Mobius.negative = SSP.sspNegOne

embedOriented : OrientedNineSheet → Cube.Ternary27Point
embedOriented ((a , b) , orientation) =
  Cube.ternary27Point (Wheel.kernelToSSP a)
                            (Wheel.kernelToSSP b)
                            (orientTrit orientation)

decodeSheet : Cube.Ternary27Point → Triadic.NineSheet
decodeSheet point = Wheel.sspToKernel (Cube.x point) ,
                    Wheel.sspToKernel (Cube.y point)

decodeOrientationOnImage : OrientedNineSheet → Mobius.OrientationPolarity
decodeOrientationOnImage state = proj₂ state

sheetRoundTrip : (state : OrientedNineSheet) →
  decodeSheet (embedOriented state) ≡ proj₁ state
sheetRoundTrip ((a , b) , orientation)
  rewrite Wheel.kernelSSPRoundTrip a
        | Wheel.kernelSSPRoundTrip b = refl

orientationOnImage :
  (state : OrientedNineSheet) →
  Cube.z (embedOriented state) ≡ orientTrit (proj₂ state)
orientationOnImage state = refl

-- Image uniqueness: an equality of embedded points determines the sheet
-- coordinates and the orientation. The latter uses a two-case constructor
-- distinction rather than identifying the neutral face with an orientation.
orientationDistinct :
  orientTrit Mobius.positive ≡ orientTrit Mobius.negative → ⊥
orientationDistinct ()

orientationDetermined : (a b : Mobius.OrientationPolarity) →
  orientTrit a ≡ orientTrit b → a ≡ b
orientationDetermined Mobius.positive Mobius.positive same = refl
orientationDetermined Mobius.positive Mobius.negative same =
  ⊥-elim (orientationDistinct same)
orientationDetermined Mobius.negative Mobius.positive ()
orientationDetermined Mobius.negative Mobius.negative same = refl

embedInjective : (a b : OrientedNineSheet) →
  embedOriented a ≡ embedOriented b → a ≡ b
embedInjective (sheetA , orientA) (sheetB , orientB) same
  with orientationDetermined orientA orientB
      (cong Cube.z same)
... | refl =
  cong₂ _,_
    (trans (sym (sheetRoundTrip (sheetA , orientA)))
      (trans (cong decodeSheet same)
        (sheetRoundTrip (sheetB , orientA))))
    refl

-- The neutral face is an explicit nine-sheet complementary plane.
neutralFace : Triadic.NineSheet → Cube.Ternary27Point
neutralFace (a , b) = Cube.ternary27Point
  (Wheel.kernelToSSP a) (Wheel.kernelToSSP b) SSP.sspZero

neutralFaceIsNotOriented :
  (sheet : Triadic.NineSheet) (state : OrientedNineSheet) →
  neutralFace sheet ≡ embedOriented state → ⊥
neutralFaceIsNotOriented sheet ((a , b) , Mobius.positive) ()
neutralFaceIsNotOriented sheet ((a , b) , Mobius.negative) ()
