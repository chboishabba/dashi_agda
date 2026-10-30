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
