module DASHI.Physics.Closure.R2P2C5FullSampledIntegerOperatorExact where

------------------------------------------------------------------------
-- FULL 125-OUTPUT SAMPLE PATH FOR THE ORIGINAL EXACT INTEGER 27x27 PAIRS.
--
-- Source owners: Full.fiveGridGroupSum, Full.wideToFiveGrid, the original
-- coefficient-polymorphic Bilinear 729-term 125-output theorem, and new
-- source Q(zeta5) character / 125-sample transform. In contrast with
-- C4 retained projection, the 5-grid distinguishes ALL -2..+2 outputs.
-- Source-written pending kernel; no physical or Monster promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Rational.Base using (ℚ; normalize)
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P227729BilinearCyclotomicPadCutExact as Bilinear
import DASHI.Physics.Closure.R2P2C5CyclotomicFullFourierCharacterExact as C5
import DASHI.Physics.Closure.R2P2C5FullSampledFourierBidiExact as FFT

inputAtFiveAxis : I.FiveGridMode → Maybe M.ThreeMode
inputAtFiveAxis I.gridZero = just M.modeZero
inputAtFiveAxis I.gridPlusOne = just M.modePlus
inputAtFiveAxis I.gridMinusOne = just M.modeMinus
inputAtFiveAxis I.gridPlusTwo = nothing
inputAtFiveAxis I.gridMinusTwo = nothing

inputToFiveAxis : M.ThreeMode → I.FiveGridMode
inputToFiveAxis M.modeMinus = I.gridMinusOne
inputToFiveAxis M.modeZero = I.gridZero
inputToFiveAxis M.modePlus = I.gridPlusOne

inputAxisRoundTrip :
  (k : M.ThreeMode) → inputAtFiveAxis (inputToFiveAxis k) ≡ just k
inputAxisRoundTrip M.modeMinus = refl
inputAxisRoundTrip M.modeZero = refl
inputAxisRoundTrip M.modePlus = refl

zeroPadded125At :
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.GridCube125 → C5.Cyclotomic5
zeroPadded125At f (Full.gridCube x y z)
  with inputAtFiveAxis x | inputAtFiveAxis y | inputAtFiveAxis z
... | just a | just b | just c = f (I.modeCube a b c)
... | _ | _ | _ = C5.zero5

pad27To125 :
  (I.ModeCube27 → C5.Cyclotomic5) → FFT.CubeSignal125
pad27To125 f =
  FFT.quintFrom λ x →
    FFT.quintFrom λ y →
      FFT.quintFrom λ z →
        zeroPadded125At f (Full.gridCube x y z)

cubeAt : FFT.CubeSignal125 → Full.GridCube125 → C5.Cyclotomic5
cubeAt xs (Full.gridCube a b c) =
  FFT.quintAt (FFT.quintAt (FFT.quintAt xs a) b) c

readRetained :
  FFT.CubeSignal125 → I.ModeCube27 → C5.Cyclotomic5
readRetained xs (I.modeCube a b c) =
  cubeAt xs (Full.gridCube
    (inputToFiveAxis a) (inputToFiveAxis b) (inputToFiveAxis c))

paddingRetainsAll27 :
  (f : I.ModeCube27 → C5.Cyclotomic5) (k : I.ModeCube27) →
  readRetained (pad27To125 f) k ≡ f k
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeMinus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeMinus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeMinus M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeZero M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeZero M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modeZero M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modePlus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modePlus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeMinus M.modePlus M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeMinus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeMinus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeMinus M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeZero M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeZero M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modeZero M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modePlus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modePlus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modeZero M.modePlus M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeMinus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeMinus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeMinus M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeZero M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeZero M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modeZero M.modePlus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modePlus M.modeMinus) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modePlus M.modeZero) = refl
paddingRetainsAll27 f (I.modeCube M.modePlus M.modePlus M.modePlus) = refl

scaleCube125 : ℚ → FFT.CubeSignal125 → FFT.CubeSignal125
scaleCube125 q =
  FFT.mapQuint (FFT.mapQuint (FFT.mapQuint (FFT.scale5 q)))

oneOver125 : ℚ
oneOver125 = normalize 1 125

whole125 : ℚ
whole125 = 125

unscaledSynthesis125 :
  FFT.CubeSignal125 → FFT.CubeSignal125
unscaledSynthesis125 spectrum =
  scaleCube125 whole125 (FFT.inverseFourier125 spectrum)

normalizedAnalysis125 :
  FFT.CubeSignal125 → FFT.CubeSignal125
normalizedAnalysis125 samples =
  scaleCube125 oneOver125 (FFT.fourier125 samples)

-- TRUE full 125-output sampled pointwise operator. Its input Fourier
-- carrier has only the original 27 supported signed integer modes.
fullSampledBilinear125 :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.WideCube125 → C5.Cyclotomic5
fullSampledBilinear125 f g target =
  cubeAt
    (normalizedAnalysis125
      (FFT.pointwiseProduct125
        (unscaledSynthesis125 (pad27To125 f))
        (unscaledSynthesis125 (pad27To125 g))))
    (Full.wideToFiveGrid target)

-- Reuse original generic coefficient convolution *with the same*
-- Q(zeta5) scalar carrier. No wrong-root coercion is performed.
cyclotomicFiveOps : Bilinear.CoefficientOps C5.Cyclotomic5
cyclotomicFiveOps = record
  { zero = C5.zero5
  ; add = C5._+5_
  ; multiply = C5._*5_
  }

originalTrue125BilinearAt :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.WideCube125 → C5.Cyclotomic5
originalTrue125BilinearAt =
  Bilinear.trueBilinearConvolutionAt cyclotomicFiveOps

indexedFiveGridBilinearAt :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.WideCube125 → C5.Cyclotomic5
indexedFiveGridBilinearAt =
  Bilinear.fiveGridBilinearFullAt cyclotomicFiveOps

indexedFiveGridEqualsTrueFullInteger :
  (f g : I.ModeCube27 → C5.Cyclotomic5)
  (target : Full.WideCube125) →
  indexedFiveGridBilinearAt f g target
    ≡ originalTrue125BilinearAt f g target
indexedFiveGridEqualsTrueFullInteger =
  Bilinear.fiveGridBilinearRecoversAllFullCoefficients cyclotomicFiveOps

-- NEXT EXACT SAME-TYPE KERNEL OBLIGATION:
--   fullSampledBilinear125 f g target
--     ≡ indexedFiveGridBilinearAt f g target.
-- The exhaustive independent Q(zeta5) character/basis test is evidence,
-- not an Agda proof of the 125-grid sampled multiplication theorem.
