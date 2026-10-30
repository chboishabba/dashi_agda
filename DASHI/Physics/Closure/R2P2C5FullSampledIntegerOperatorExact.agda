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
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Agda.Builtin.List using (List)
open import Data.Product using (_,_; proj₁; proj₂)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Rational.Base using (ℚ; normalize)
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P2C4C5NyquistAntipodalFixedPointExact as Nyquist
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
whole125 = normalize 125 1

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


------------------------------------------------------------------------
-- SAME-OBJECT CYCLOTOMIC FINITE FUBINI/SCALING INSTANTIATION.
-- Reuses source Yang--Mills and NS finite sum proofs via the generic
-- coefficient-polymorphic interface in BilinearCyclotomicPadCutExact.
-- Needed for the actual 3D FFT sampled→index distribution proof;
-- it is not yet that theorem.
------------------------------------------------------------------------

cyclotomicFiveFiniteSumAlgebra : Bilinear.FiniteSumAlgebra cyclotomicFiveOps
cyclotomicFiveFiniteSumAlgebra = record
  { sumAddAssoc = C5.scalarAddAssociative
  ; sumAddComm = C5.scalarAddCommutative
  ; sumAddZeroLeft = C5.scalarAddZeroLeft
  ; sumMulDistributesLeft = C5.scalarMulDistributesLeft
  ; sumMulDistributesRight = C5.scalarMulDistributesRight
  ; sumMulAssociative = C5.scalarMulAssociative
  ; sumMulCommutative = C5.scalarMulCommutative
  ; sumMulZeroLeft = C5.scalarMulZeroLeft
  ; sumMulZeroRight = C5.scalarMulZeroRight
  }

cyclotomicFiveActualFiniteSumSwap :
  ∀ {X Y : Set} (xs : List X)
  (ys : List Y)
  (f : X → Y → C5.Cyclotomic5) →
  Bilinear.sumAll cyclotomicFiveOps xs
    (λ x → Bilinear.sumAll cyclotomicFiveOps ys (f x))
  ≡ Bilinear.sumAll cyclotomicFiveOps ys
    (λ y → Bilinear.sumAll cyclotomicFiveOps xs (λ x → f x y))
cyclotomicFiveActualFiniteSumSwap =
  Bilinear.sumAllSwap cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra

cyclotomicFiveActualFiniteSumProductScale :
  ∀ {X : Set} (z : C5.Cyclotomic5)
  (xs : List X) (f : X → C5.Cyclotomic5) →
  Bilinear.sumAll cyclotomicFiveOps xs
    (λ x → C5._*5_ z (f x))
  ≡ C5._*5_ z
      (Bilinear.sumAll cyclotomicFiveOps xs f)
cyclotomicFiveActualFiniteSumProductScale =
  Bilinear.sumAllScaleLeft cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra


-- This is the genuine distributive Fourier-field product expansion,
-- over the ORIGINAL source 729 ordered input pair addresses.
cyclotomicFiveActual729InputProductExpansion :
  (f g : I.ModeCube27 → C5.Cyclotomic5) →
  C5._*5_
    (Bilinear.sumAll cyclotomicFiveOps I.cube27 f)
    (Bilinear.sumAll cyclotomicFiveOps I.cube27 g)
  ≡ Bilinear.sumAll cyclotomicFiveOps I.pair729
      (λ pair → C5._*5_
        (f (proj₁ pair)) (g (proj₂ pair)))
cyclotomicFiveActual729InputProductExpansion =
  Bilinear.source729ProductExpansion
    cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra


------------------------------------------------------------------------
-- LITERAL SOURCE-MODE CHARACTER EXPANSION AT EACH FINITE SAMPLE POINT.
--
-- This is the missing raw-product bridge for the actual existing
-- Full.GridCube125 cyclic sample carrier: any TWO independent original
-- 27-mode fields produce the ORIGINAL 729 ordered input products,
-- each weighted by the character of the actual group-summed index.
-- This is NOT yet the normalized forward transform or integer-output
-- projection: that still requires complete 3D character resolution.
------------------------------------------------------------------------

cyclotomicFiveCubeCharacter :
  Full.GridCube125 → Full.GridCube125 → C5.Cyclotomic5
cyclotomicFiveCubeCharacter
  (Full.gridCube a b c) (Full.gridCube x y z) =
  C5._*5_ (C5._*5_ (C5.character5 a x) (C5.character5 b y)) (C5.character5 c z)

cyclotomicFiveCubeCharacterAddition :
  (p q x : Full.GridCube125) →
  cyclotomicFiveCubeCharacter (Full.fiveGridGroupSum p q) x
  ≡ C5._*5_ (cyclotomicFiveCubeCharacter p x) (cyclotomicFiveCubeCharacter q x)
cyclotomicFiveCubeCharacterAddition
  (Full.gridCube a b c) (Full.gridCube d e f)
  (Full.gridCube x y z)
  rewrite C5.characterAdditionLaw a d x
        | C5.characterAdditionLaw b e y
        | C5.characterAdditionLaw c f z =
  Bilinear.productShuffleSix cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
    (C5.character5 a x) (C5.character5 d x)
    (C5.character5 b y) (C5.character5 e y)
    (C5.character5 c z) (C5.character5 f z)

cyclotomicFiveOriginal27UnscaledSynthesisAt :
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.GridCube125 → C5.Cyclotomic5
cyclotomicFiveOriginal27UnscaledSynthesisAt f x =
  Bilinear.sumAll cyclotomicFiveOps I.cube27
    (λ p → C5._*5_ (f p) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid p) x))

cyclotomicFiveOriginal729PhaseContribution :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.GridCube125 → I.ModePair729 → C5.Cyclotomic5
cyclotomicFiveOriginal729PhaseContribution f g x (p , q) =
  C5._*5_ (C5._*5_ (f p) (g q)) (cyclotomicFiveCubeCharacter (Full.fiveGridGroupSum (Full.inputToFiveGrid p) (Full.inputToFiveGrid q)) x)

cyclotomicFiveSourceSampledProductExpands729 :
  (f g : I.ModeCube27 → C5.Cyclotomic5)
  (x : Full.GridCube125) →
  C5._*5_ (cyclotomicFiveOriginal27UnscaledSynthesisAt f x) (cyclotomicFiveOriginal27UnscaledSynthesisAt g x)
  ≡ Bilinear.sumAll cyclotomicFiveOps I.pair729
      (cyclotomicFiveOriginal729PhaseContribution f g x)
cyclotomicFiveSourceSampledProductExpands729 f g x =
  trans
    (Bilinear.source729ProductExpansion cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
      (λ p → C5._*5_ (f p) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid p) x))
      (λ q → C5._*5_ (g q) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid q) x)))
    (Bilinear.sumAllCong cyclotomicFiveOps I.pair729
      (λ pair →
        C5._*5_ (C5._*5_ (f (proj₁ pair)) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid (proj₁ pair)) x)) (C5._*5_ (g (proj₂ pair)) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid (proj₂ pair)) x)))
      (cyclotomicFiveOriginal729PhaseContribution f g x)
      (λ { (p , q) →
        trans
          (Bilinear.productShuffle4 cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
            (f p) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid p) x)
            (g q) (cyclotomicFiveCubeCharacter (Full.inputToFiveGrid q) x))
          (cong (λ χ → C5._*5_ (C5._*5_ (f p) (g q)) (χ))
            (sym (cyclotomicFiveCubeCharacterAddition
              (Full.inputToFiveGrid p) (Full.inputToFiveGrid q) x))) }))

-- The original carrier/table and ordered pair list occur literally.
-- Source-written only until pinned Agda kernel checks the full module.

------------------------------------------------------------------------
-- FINITE SAMPLE EXTRACTION AT THE ORIGINAL C5 full 125 TARGETS.
-- Explicit character resolution remains an INPUT, not an axiom or a
-- synthetic receipt. Reuses the generic 729/finite-Fubini compiler
-- instead of a second indexed convolution or a wrong scalar carrier.
------------------------------------------------------------------------

cyclotomicFiveSelectedOriginalPair :
  Full.WideCube125 → I.ModePair729 → Bool
cyclotomicFiveSelectedOriginalPair target (p , q) =
  Full.eqWideCube
    (Full.fiveGridToWide
      (Full.fiveGridGroupSum (Full.inputToFiveGrid p) (Full.inputToFiveGrid q)))
    target

cyclotomicFiveNormalizedCharacterPhase :
  Full.WideCube125 → I.ModePair729 → Full.GridCube125 → C5.Cyclotomic5
cyclotomicFiveNormalizedCharacterPhase target (p , q) x =
  FFT.scale5 oneOver125
    (C5._*5_
      (cyclotomicFiveCubeCharacter
        (Full.fiveGridGroupSum (Full.inputToFiveGrid p) (Full.inputToFiveGrid q)) x)
      (C5.conj5
        (cyclotomicFiveCubeCharacter (Full.wideToFiveGrid target) x)))

cyclotomicFiveOriginalPairCoefficient :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  I.ModePair729 → C5.Cyclotomic5
cyclotomicFiveOriginalPairCoefficient f g (p , q) =
  C5._*5_ (f p) (g q)

cyclotomicFiveSourceNormalizedSampledAt :
  (I.ModeCube27 → C5.Cyclotomic5) →
  (I.ModeCube27 → C5.Cyclotomic5) →
  Full.WideCube125 → C5.Cyclotomic5
cyclotomicFiveSourceNormalizedSampledAt f g target =
  Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveGridCubes
    (λ x → Bilinear.sumAll cyclotomicFiveOps I.pair729
      (λ pair → C5._*5_
        (cyclotomicFiveOriginalPairCoefficient f g pair)
        (cyclotomicFiveNormalizedCharacterPhase target pair x)))

cyclotomicFiveActualCharacterResolution :
  Full.WideCube125 → Set
cyclotomicFiveActualCharacterResolution target =
  (pair : I.ModePair729) →
  Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveGridCubes
    (cyclotomicFiveNormalizedCharacterPhase target pair)
  ≡ Bilinear.choose C5.zero5
    (cyclotomicFiveSelectedOriginalPair target pair) C5.one5

cyclotomicFiveSourceSampledEqualsIndexedGivenResolution :
  (f g : I.ModeCube27 → C5.Cyclotomic5)
  (target : Full.WideCube125) →
  cyclotomicFiveActualCharacterResolution target →
  cyclotomicFiveSourceNormalizedSampledAt f g target
    ≡ indexedFiveGridBilinearAt f g target
cyclotomicFiveSourceSampledEqualsIndexedGivenResolution f g target resolution =
  Bilinear.finiteFourierExtractionFromOriginal729GivenResolution
    cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
    Nyquist.allFiveGridCubes
    C5.one5 C5.scalarMulOneRight
    (cyclotomicFiveOriginalPairCoefficient f g)
    (cyclotomicFiveNormalizedCharacterPhase target)
    (cyclotomicFiveSelectedOriginalPair target)
    resolution

-- The condition above is the 64/125-character resolution,
-- not the missing tensor-FFT synthesis/analysis same-object theorem.
-- Neither is silently assumed from a numeric Python fixture.


------------------------------------------------------------------------
-- FIRST ACTUALLY DISCHARGED SOURCE-ORDER CHARACTER-RESOLUTION LEAF.
-- Uses exact ORIGINAL Nyquist axis enumeration (not the phase owner's
-- alternative cyclic listing), original character/group equality,
-- and the original Q(i)/Q(zeta5) coefficient operations.
--
-- Finite 4² / 5² patterns, no postulate and no list-equality oracle.
-- This is ONE AXIS.  Three-axis Fubini and the tensor FFT identification
-- are separate downstream kernel obligations.
------------------------------------------------------------------------

cyclotomicFiveSourceAxisCharacterKernel :
  I.FiveGridMode → I.FiveGridMode → C5.Cyclotomic5
cyclotomicFiveSourceAxisCharacterKernel k l =
  Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes
    (λ x →
      FFT.scale5 FFT.oneFifth
        (C5._*5_ (C5.character5 k x)
          (C5.conj5 (C5.character5 l x))))

cyclotomicFiveOriginalAxisCharacterResolution :
  (k l : I.FiveGridMode) →
  cyclotomicFiveSourceAxisCharacterKernel k l
  ≡ Bilinear.choose C5.zero5 (C5.eq5 k l) C5.one5
cyclotomicFiveOriginalAxisCharacterResolution I.gridZero I.gridZero = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridZero I.gridPlusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridZero I.gridPlusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridZero I.gridMinusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridZero I.gridMinusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusOne I.gridZero = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusOne I.gridPlusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusOne I.gridPlusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusOne I.gridMinusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusOne I.gridMinusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusTwo I.gridZero = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusTwo I.gridPlusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusTwo I.gridPlusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusTwo I.gridMinusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridPlusTwo I.gridMinusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusTwo I.gridZero = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusTwo I.gridPlusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusTwo I.gridPlusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusTwo I.gridMinusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusTwo I.gridMinusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusOne I.gridZero = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusOne I.gridPlusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusOne I.gridPlusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusOne I.gridMinusTwo = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
cyclotomicFiveOriginalAxisCharacterResolution I.gridMinusOne I.gridMinusOne = C5.cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

-- Actual enumerated axes are owned by R2P2C4C5NyquistAntipodalFixedPointExact.
-- Source-written proof terms; an Agda kernel run is still required.


------------------------------------------------------------------------
-- ORIGINAL SOURCE CUBE ENUMERATION: now exactly triple-Fubini,
-- reusing the one generic semiring proof and existing Nyquist lists.
-- Nothing requires an artificial parallel cube indexed by Z/4 or Z/5.
------------------------------------------------------------------------

cyclotomicFiveActualNyquistSumAsNested :
  (term : Full.GridCube125 → C5.Cyclotomic5) →
  Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveGridCubes term
  ≡ Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes
      (λ x → Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes
        (λ y → Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes
          (λ z → term (Full.gridCube x y z))))
cyclotomicFiveActualNyquistSumAsNested =
  Bilinear.sourceCartesianTripleSumWith
    cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
    Nyquist.allFiveAxes Nyquist.allFiveAxes Nyquist.allFiveAxes
    Full.gridCube

cyclotomicFiveActualNyquistSeparableProduct :
  (fx fy fz : I.FiveGridMode → C5.Cyclotomic5)
  (cubeTerm : Full.GridCube125 → C5.Cyclotomic5) →
  ((x y z : I.FiveGridMode) →
    cubeTerm (Full.gridCube x y z)
    ≡ C5._*5_
      (C5._*5_ (fx x) (fy y))
      (fz z)) →
  Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveGridCubes cubeTerm
  ≡ C5._*5_
      (C5._*5_
        (Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes fx)
        (Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes fy))
      (Bilinear.sumAll cyclotomicFiveOps Nyquist.allFiveAxes fz)
cyclotomicFiveActualNyquistSeparableProduct fx fy fz cubeTerm agreement =
  Bilinear.sourceCartesianTripleProductFactorsWith
    cyclotomicFiveOps cyclotomicFiveFiniteSumAlgebra
    Nyquist.allFiveAxes Nyquist.allFiveAxes Nyquist.allFiveAxes
    Full.gridCube fx fy fz cubeTerm agreement
