module DASHI.Physics.Closure.R2P2C4RetainedSampledOperatorExact where

------------------------------------------------------------------------
-- OPERATOR-LEVEL C4^3 SAMPLE PATH FOR 27 EXACT INTEGER FOURIER MODES.
--
-- Distinct source owners:
--  R2P227729FourierObserverIncidenceExact (27 actual signed inputs)
--  R2P227729FourGridRetainedQuadraticParetoExact (Z/4 indices)
--  R2P2C4GaussianFourierCharacterExact (exact Q(i))
--  R2P2C4GaussianSampledFourierBidiExact (actual 64-sample FFT/inverse)
--  R2P227729BilinearCyclotomicPadCutExact (generic 729 interactions).
--
-- This adapter is about ACTUAL normalized sampled-field operations,
-- not merely a precomputed cyclic pair-index sum. It deliberately uses
-- Q(i) instead of silently casting the earlier C3 Q(omega) carrier.
-- Full pair coefficient equality remains a distinct kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Rational.Base using (ℚ; _*_; normalize)
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as Four
import DASHI.Physics.Closure.R2P2C4GaussianFourierCharacterExact as G
import DASHI.Physics.Closure.R2P2C4GaussianSampledFourierBidiExact as FFT

-- A 4-grid has one extra frequency: Nyquist residue 2.
-- Inputs at this residue are always ZERO, not undefined.
axisFromFour : Four.FourGridMode → Maybe M.ThreeMode
axisFromFour Four.fourZero = just M.modeZero
axisFromFour Four.fourPlusOne = just M.modePlus
axisFromFour Four.fourMinusOne = just M.modeMinus
axisFromFour Four.fourOuterTwo = nothing

axisToFour : M.ThreeMode → Four.FourGridMode
axisToFour M.modeMinus = Four.fourMinusOne
axisToFour M.modeZero = Four.fourZero
axisToFour M.modePlus = Four.fourPlusOne

axisInputSection :
  (k : M.ThreeMode) → axisFromFour (axisToFour k) ≡ just k
axisInputSection M.modeMinus = refl
axisInputSection M.modeZero = refl
axisInputSection M.modePlus = refl

-- The sample-domain array ordering is the GROUP order 0,+1,2,-1.
-- It must not be confused with the display order -1,0,+1,2.
quadFromFunction :
  ∀ {A : Set} →
  (Four.FourGridMode → A) → FFT.Quad A
quadFromFunction f =
  FFT.quad (f Four.fourZero) (f Four.fourPlusOne)
           (f Four.fourOuterTwo) (f Four.fourMinusOne)

quadAt :
  ∀ {A : Set} → FFT.Quad A → Four.FourGridMode → A
quadAt (FFT.quad a b c d) Four.fourZero = a
quadAt (FFT.quad a b c d) Four.fourPlusOne = b
quadAt (FFT.quad a b c d) Four.fourOuterTwo = c
quadAt (FFT.quad a b c d) Four.fourMinusOne = d

quadFunctionSection :
  ∀ {A : Set} (f : Four.FourGridMode → A)
  (k : Four.FourGridMode) →
  quadAt (quadFromFunction f) k ≡ f k
quadFunctionSection f Four.fourZero = refl
quadFunctionSection f Four.fourPlusOne = refl
quadFunctionSection f Four.fourOuterTwo = refl
quadFunctionSection f Four.fourMinusOne = refl

cubeAt : FFT.CubeSignal64 → Four.FourGridCube64 → G.Gaussian4
cubeAt xs (Four.fourCube a b c) =
  quadAt (quadAt (quadAt xs a) b) c

zeroPaddedAt :
  (I.ModeCube27 → G.Gaussian4) →
  Four.FourGridCube64 → G.Gaussian4
zeroPaddedAt f (Four.fourCube a b c)
  with axisFromFour a | axisFromFour b | axisFromFour c
... | just x | just y | just z = f (I.modeCube x y z)
... | _ | _ | _ = G.zeroG

pad27To64 :
  (I.ModeCube27 → G.Gaussian4) → FFT.CubeSignal64
pad27To64 f =
  quadFromFunction λ a →
    quadFromFunction λ b →
      quadFromFunction λ c →
        zeroPaddedAt f (Four.fourCube a b c)

cubeAtPad :
  (f : I.ModeCube27 → G.Gaussian4)
  (a b c : Four.FourGridMode) →
  cubeAt (pad27To64 f) (Four.fourCube a b c)
  ≡ zeroPaddedAt f (Four.fourCube a b c)
cubeAtPad f a b c =
  trans
    (cong (λ rows → quadAt (quadAt rows b) c)
      (quadFunctionSection outerF a))
    (trans
      (cong (λ row → quadAt row c)
        (quadFunctionSection (middleF a) b))
      (quadFunctionSection (innerF a b) c))
  where
    innerF : (x y : Four.FourGridMode) →
      Four.FourGridMode → G.Gaussian4
    innerF x y z = zeroPaddedAt f (Four.fourCube x y z)

    middleF : Four.FourGridMode →
      Four.FourGridMode → FFT.Quad G.Gaussian4
    middleF x y = quadFromFunction (innerF x y)

    outerF : Four.FourGridMode →
      FFT.Quad (FFT.Quad G.Gaussian4)
    outerF x = quadFromFunction (middleF x)

-- Select retained INTEGER wavevectors only, without folding Nyquist.
readRetained :
  FFT.CubeSignal64 → I.ModeCube27 → G.Gaussian4
readRetained xs (I.modeCube a b c) =
  cubeAt xs (Four.fourCube (axisToFour a) (axisToFour b) (axisToFour c))

paddingRetainsAll27 :
  (f : I.ModeCube27 → G.Gaussian4)
  (k : I.ModeCube27) →
  readRetained (pad27To64 f) k ≡ f k
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

-- Forward has no 1/64 factor; inverse has it. Use the following exact
-- scaling to implement the *conventional* synthesis/analysis pair.
scaleCube : ℚ → FFT.CubeSignal64 → FFT.CubeSignal64
scaleCube q =
  FFT.mapQuad (FFT.mapQuad (FFT.mapQuad (FFT.scaleG q)))

norm64 : ℚ
norm64 = normalize 1 64

unnorm64 : ℚ
unnorm64 = normalize 64 1

synthesiseUnscaled :
  FFT.CubeSignal64 → FFT.CubeSignal64
synthesiseUnscaled spectrum =
  scaleCube unnorm64 (FFT.inverseFourier64 spectrum)

analyseNormalized :
  FFT.CubeSignal64 → FFT.CubeSignal64
analyseNormalized sampled =
  scaleCube norm64 (FFT.fourier64 sampled)

-- The actual finite grid algorithm:
--   27 signed integer coefficients
--   -> 64 zero-padded Fourier coefficients
--   -> exact unscaled inverse synthesis at 64 samples
--   -> 64 pointwise multiplications
--   -> 1/64-normalized forward analysis
--   -> project onto the retained [-1,0,+1]^3 wavevectors.
retainedSampledBilinear :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  I.ModeCube27 → G.Gaussian4
retainedSampledBilinear f g target =
  readRetained
    (analyseNormalized
      (FFT.pointwiseProduct64
        (synthesiseUnscaled (pad27To64 f))
        (synthesiseUnscaled (pad27To64 g))))
    target

-- Source-written, not Agda kernel-checked. The 19683 symbolic basis
-- coefficients were independently exhaustively checked in the associated
-- Python certificate. A standalone kernel proof of equality with the
-- original 729-pair true-integer convolution remains open.


------------------------------------------------------------------------
-- EXACT SAME Q(i) SCALAR CARRIER AT THE INDEX-OPERATOR BOUNDARY.
-- The inherited bilinear theorem is coefficient-polymorphic and
-- supplies the correct integer/4-grid correspondence WITHOUT recasting
-- the original C3/Q(omega) amplitudes as a different scalar field.
------------------------------------------------------------------------
import DASHI.Physics.Closure.R2P227729BilinearCyclotomicPadCutExact as Bilinear
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P2C4C5NyquistAntipodalFixedPointExact as Nyquist

gaussianCoefficientOps : Bilinear.CoefficientOps G.Gaussian4
gaussianCoefficientOps = record
  { zero = G.zeroG
  ; add = G._+G_
  ; multiply = G._*G_
  }

trueGaussianIntegerConvolutionAt :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  Full.WideCube125 → G.Gaussian4
trueGaussianIntegerConvolutionAt =
  Bilinear.trueBilinearConvolutionAt gaussianCoefficientOps

fourGridGaussianIndexConvolutionAt :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  I.ModeCube27 → G.Gaussian4
fourGridGaussianIndexConvolutionAt =
  Bilinear.fourGridBilinearRetainedAt gaussianCoefficientOps

-- Fully quantified for TWO INDEPENDENT Q(i) coefficient fields,
-- not just one tested numerical profile or a formal cardinality.
fourGridGaussianIndexIsTrueIntegerConvolution :
  (f g : I.ModeCube27 → G.Gaussian4) (target : I.ModeCube27) →
  fourGridGaussianIndexConvolutionAt f g target
    ≡ trueGaussianIntegerConvolutionAt f g (Full.retainedToWide target)
fourGridGaussianIndexIsTrueIntegerConvolution =
  Bilinear.fourGridBilinearRecoversAllRetainedCoefficients gaussianCoefficientOps

-- THE remaining same-carrier sampled operator proof must relate:
--   retainedSampledBilinear f g target
--   fourGridGaussianIndexConvolutionAt f g target
-- via the exact C4^3 root character, distributivity and 1/64 scaling.
-- Do not introduce a postulate or assert an equality until proved.


------------------------------------------------------------------------
-- SAME-OBJECT CYCLOTOMIC FINITE FUBINI/SCALING INSTANTIATION.
-- Reuses source Yang--Mills and NS finite sum proofs via the generic
-- coefficient-polymorphic interface in BilinearCyclotomicPadCutExact.
-- Needed for the actual 3D FFT sampled→index distribution proof;
-- it is not yet that theorem.
------------------------------------------------------------------------

gaussianFiniteSumAlgebra : Bilinear.FiniteSumAlgebra gaussianCoefficientOps
gaussianFiniteSumAlgebra = record
  { sumAddAssoc = G.scalarAddAssociative
  ; sumAddComm = G.scalarAddCommutative
  ; sumAddZeroLeft = G.scalarAddZeroLeft
  ; sumMulDistributesLeft = G.scalarMulDistributesLeft
  ; sumMulDistributesRight = G.scalarMulDistributesRight
  ; sumMulAssociative = G.scalarMulAssociative
  ; sumMulCommutative = G.scalarMulCommutative
  ; sumMulZeroLeft = G.scalarMulZeroLeft
  ; sumMulZeroRight = G.scalarMulZeroRight
  }

gaussianActualFiniteSumSwap :
  ∀ {X Y : Set} (xs : List X)
  (ys : List Y)
  (f : X → Y → G.Gaussian4) →
  Bilinear.sumAll gaussianCoefficientOps xs
    (λ x → Bilinear.sumAll gaussianCoefficientOps ys (f x))
  ≡ Bilinear.sumAll gaussianCoefficientOps ys
    (λ y → Bilinear.sumAll gaussianCoefficientOps xs (λ x → f x y))
gaussianActualFiniteSumSwap =
  Bilinear.sumAllSwap gaussianCoefficientOps gaussianFiniteSumAlgebra

gaussianActualFiniteSumProductScale :
  ∀ {X : Set} (z : G.Gaussian4)
  (xs : List X) (f : X → G.Gaussian4) →
  Bilinear.sumAll gaussianCoefficientOps xs
    (λ x → G._*G_ z (f x))
  ≡ G._*G_ z
      (Bilinear.sumAll gaussianCoefficientOps xs f)
gaussianActualFiniteSumProductScale =
  Bilinear.sumAllScaleLeft gaussianCoefficientOps gaussianFiniteSumAlgebra


-- This is the genuine distributive Fourier-field product expansion,
-- over the ORIGINAL source 729 ordered input pair addresses.
gaussianActual729InputProductExpansion :
  (f g : I.ModeCube27 → G.Gaussian4) →
  G._*G_
    (Bilinear.sumAll gaussianCoefficientOps I.cube27 f)
    (Bilinear.sumAll gaussianCoefficientOps I.cube27 g)
  ≡ Bilinear.sumAll gaussianCoefficientOps I.pair729
      (λ pair → G._*G_
        (f (proj₁ pair)) (g (proj₂ pair)))
gaussianActual729InputProductExpansion =
  Bilinear.source729ProductExpansion
    gaussianCoefficientOps gaussianFiniteSumAlgebra


------------------------------------------------------------------------
-- LITERAL SOURCE-MODE CHARACTER EXPANSION AT EACH FINITE SAMPLE POINT.
--
-- This is the missing raw-product bridge for the actual existing
-- Four.FourGridCube64 cyclic sample carrier: any TWO independent original
-- 27-mode fields produce the ORIGINAL 729 ordered input products,
-- each weighted by the character of the actual group-summed index.
-- This is NOT yet the normalized forward transform or integer-output
-- projection: that still requires complete 3D character resolution.
------------------------------------------------------------------------

gaussianCubeCharacter :
  Four.FourGridCube64 → Four.FourGridCube64 → G.Gaussian4
gaussianCubeCharacter
  (Four.fourCube a b c) (Four.fourCube x y z) =
  G._*G_ (G._*G_ (G.character4 a x) (G.character4 b y)) (G.character4 c z)

gaussianCubeCharacterAddition :
  (p q x : Four.FourGridCube64) →
  gaussianCubeCharacter (Four.fourGridGroupSum p q) x
  ≡ G._*G_ (gaussianCubeCharacter p x) (gaussianCubeCharacter q x)
gaussianCubeCharacterAddition
  (Four.fourCube a b c) (Four.fourCube d e f)
  (Four.fourCube x y z)
  rewrite G.characterAdditionLaw a d x
        | G.characterAdditionLaw b e y
        | G.characterAdditionLaw c f z =
  Bilinear.productShuffleSix gaussianCoefficientOps gaussianFiniteSumAlgebra
    (G.character4 a x) (G.character4 d x)
    (G.character4 b y) (G.character4 e y)
    (G.character4 c z) (G.character4 f z)

gaussianOriginal27UnscaledSynthesisAt :
  (I.ModeCube27 → G.Gaussian4) →
  Four.FourGridCube64 → G.Gaussian4
gaussianOriginal27UnscaledSynthesisAt f x =
  Bilinear.sumAll gaussianCoefficientOps I.cube27
    (λ p → G._*G_ (f p) (gaussianCubeCharacter (Four.inputToFourGrid p) x))

gaussianOriginal729PhaseContribution :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  Four.FourGridCube64 → I.ModePair729 → G.Gaussian4
gaussianOriginal729PhaseContribution f g x (p , q) =
  G._*G_ (G._*G_ (f p) (g q)) (gaussianCubeCharacter (Four.fourGridGroupSum (Four.inputToFourGrid p) (Four.inputToFourGrid q)) x)

gaussianSourceSampledProductExpands729 :
  (f g : I.ModeCube27 → G.Gaussian4)
  (x : Four.FourGridCube64) →
  G._*G_ (gaussianOriginal27UnscaledSynthesisAt f x) (gaussianOriginal27UnscaledSynthesisAt g x)
  ≡ Bilinear.sumAll gaussianCoefficientOps I.pair729
      (gaussianOriginal729PhaseContribution f g x)
gaussianSourceSampledProductExpands729 f g x =
  trans
    (Bilinear.source729ProductExpansion gaussianCoefficientOps gaussianFiniteSumAlgebra
      (λ p → G._*G_ (f p) (gaussianCubeCharacter (Four.inputToFourGrid p) x))
      (λ q → G._*G_ (g q) (gaussianCubeCharacter (Four.inputToFourGrid q) x)))
    (Bilinear.sumAllCong gaussianCoefficientOps I.pair729
      (λ pair →
        G._*G_ (G._*G_ (f (proj₁ pair)) (gaussianCubeCharacter (Four.inputToFourGrid (proj₁ pair)) x)) (G._*G_ (g (proj₂ pair)) (gaussianCubeCharacter (Four.inputToFourGrid (proj₂ pair)) x)))
      (gaussianOriginal729PhaseContribution f g x)
      (λ { (p , q) →
        trans
          (Bilinear.productShuffle4 gaussianCoefficientOps gaussianFiniteSumAlgebra
            (f p) (gaussianCubeCharacter (Four.inputToFourGrid p) x)
            (g q) (gaussianCubeCharacter (Four.inputToFourGrid q) x))
          (cong (λ χ → G._*G_ (G._*G_ (f p) (g q)) (χ))
            (sym (gaussianCubeCharacterAddition
              (Four.inputToFourGrid p) (Four.inputToFourGrid q) x))) }))

-- The original carrier/table and ordered pair list occur literally.
-- Source-written only until pinned Agda kernel checks the full module.

------------------------------------------------------------------------
-- FINITE SAMPLE EXTRACTION AT THE ORIGINAL C4 retained 27 TARGETS.
-- Explicit character resolution remains an INPUT, not an axiom or a
-- synthetic receipt. Reuses the generic 729/finite-Fubini compiler
-- instead of a second indexed convolution or a wrong scalar carrier.
------------------------------------------------------------------------

gaussianSelectedOriginalPair :
  I.ModeCube27 → I.ModePair729 → Bool
gaussianSelectedOriginalPair target (p , q) =
  Four.eqFourCube
    (Four.fourGridGroupSum (Four.inputToFourGrid p) (Four.inputToFourGrid q))
    (Four.wideToFourGrid (Full.retainedToWide target))

gaussianNormalizedCharacterPhase :
  I.ModeCube27 → I.ModePair729 → Four.FourGridCube64 → G.Gaussian4
gaussianNormalizedCharacterPhase target (p , q) x =
  FFT.scaleG norm64
    (G._*G_
      (gaussianCubeCharacter
        (Four.fourGridGroupSum (Four.inputToFourGrid p) (Four.inputToFourGrid q)) x)
      (G.conjG
        (gaussianCubeCharacter (Four.wideToFourGrid (Full.retainedToWide target)) x)))

gaussianOriginalPairCoefficient :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  I.ModePair729 → G.Gaussian4
gaussianOriginalPairCoefficient f g (p , q) =
  G._*G_ (f p) (g q)

gaussianSourceNormalizedSampledAt :
  (I.ModeCube27 → G.Gaussian4) →
  (I.ModeCube27 → G.Gaussian4) →
  I.ModeCube27 → G.Gaussian4
gaussianSourceNormalizedSampledAt f g target =
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourGridCubes
    (λ x → Bilinear.sumAll gaussianCoefficientOps I.pair729
      (λ pair → G._*G_
        (gaussianOriginalPairCoefficient f g pair)
        (gaussianNormalizedCharacterPhase target pair x)))

gaussianActualCharacterResolution :
  I.ModeCube27 → Set
gaussianActualCharacterResolution target =
  (pair : I.ModePair729) →
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourGridCubes
    (gaussianNormalizedCharacterPhase target pair)
  ≡ Bilinear.choose G.zeroG
    (gaussianSelectedOriginalPair target pair) G.oneG

gaussianSourceSampledEqualsIndexedGivenResolution :
  (f g : I.ModeCube27 → G.Gaussian4)
  (target : I.ModeCube27) →
  gaussianActualCharacterResolution target →
  gaussianSourceNormalizedSampledAt f g target
    ≡ fourGridGaussianIndexConvolutionAt f g target
gaussianSourceSampledEqualsIndexedGivenResolution f g target resolution =
  Bilinear.finiteFourierExtractionFromOriginal729GivenResolution
    gaussianCoefficientOps gaussianFiniteSumAlgebra
    Nyquist.allFourGridCubes
    G.oneG G.scalarMulOneRight
    (gaussianOriginalPairCoefficient f g)
    (gaussianNormalizedCharacterPhase target)
    (gaussianSelectedOriginalPair target)
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

gaussianSourceAxisCharacterKernel :
  Four.FourGridMode → Four.FourGridMode → G.Gaussian4
gaussianSourceAxisCharacterKernel k l =
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes
    (λ x →
      FFT.scaleG FFT.quarter
        (G._*G_ (G.character4 k x)
          (G.conjG (G.character4 l x))))

gaussianOriginalAxisCharacterResolution :
  (k l : Four.FourGridMode) →
  gaussianSourceAxisCharacterKernel k l
  ≡ Bilinear.choose G.zeroG (Four.eqFour k l) G.oneG
gaussianOriginalAxisCharacterResolution Four.fourZero Four.fourZero = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourZero Four.fourPlusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourZero Four.fourOuterTwo = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourZero Four.fourMinusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourPlusOne Four.fourZero = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourPlusOne Four.fourPlusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourPlusOne Four.fourOuterTwo = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourPlusOne Four.fourMinusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourOuterTwo Four.fourZero = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourOuterTwo Four.fourPlusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourOuterTwo Four.fourOuterTwo = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourOuterTwo Four.fourMinusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourMinusOne Four.fourZero = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourMinusOne Four.fourPlusOne = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourMinusOne Four.fourOuterTwo = G.gauss-ext solve-∀ solve-∀
gaussianOriginalAxisCharacterResolution Four.fourMinusOne Four.fourMinusOne = G.gauss-ext solve-∀ solve-∀

-- Actual enumerated axes are owned by R2P2C4C5NyquistAntipodalFixedPointExact.
-- Source-written proof terms; an Agda kernel run is still required.


------------------------------------------------------------------------
-- ORIGINAL SOURCE CUBE ENUMERATION: now exactly triple-Fubini,
-- reusing the one generic semiring proof and existing Nyquist lists.
-- Nothing requires an artificial parallel cube indexed by Z/4 or Z/5.
------------------------------------------------------------------------

gaussianActualNyquistSumAsNested :
  (term : Four.FourGridCube64 → G.Gaussian4) →
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourGridCubes term
  ≡ Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes
      (λ x → Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes
        (λ y → Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes
          (λ z → term (Four.fourCube x y z))))
gaussianActualNyquistSumAsNested =
  Bilinear.sourceCartesianTripleSumWith
    gaussianCoefficientOps gaussianFiniteSumAlgebra
    Nyquist.allFourAxes Nyquist.allFourAxes Nyquist.allFourAxes
    Four.fourCube

gaussianActualNyquistSeparableProduct :
  (fx fy fz : Four.FourGridMode → G.Gaussian4)
  (cubeTerm : Four.FourGridCube64 → G.Gaussian4) →
  ((x y z : Four.FourGridMode) →
    cubeTerm (Four.fourCube x y z)
    ≡ G._*G_
      (G._*G_ (fx x) (fy y))
      (fz z)) →
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourGridCubes cubeTerm
  ≡ G._*G_
      (G._*G_
        (Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes fx)
        (Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes fy))
      (Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourAxes fz)
gaussianActualNyquistSeparableProduct fx fy fz cubeTerm agreement =
  Bilinear.sourceCartesianTripleProductFactorsWith
    gaussianCoefficientOps gaussianFiniteSumAlgebra
    Nyquist.allFourAxes Nyquist.allFourAxes Nyquist.allFourAxes
    Four.fourCube fx fy fz cubeTerm agreement


------------------------------------------------------------------------
-- EXACT THREE-AXIS CHARACTER NORMALIZATION AND CONJUGATE REGROUPING.
-- Reuses the original cyclotomic conjugation and four-factor product
-- permuter; two-factor scale-product proved in existing FFT owner.
-- No 4^6 / 5^6 exhaustive constructor explosion or new scalar field.
------------------------------------------------------------------------

gaussianCubeScaleFactor :
  norm64 ≡ (FFT.quarter * FFT.quarter) * FFT.quarter
gaussianCubeScaleFactor = solve-∀

gaussianTripleNormalizedPhaseScale :
  (a b c d e f : G.Gaussian4) →
  FFT.scaleG norm64 (G._*G_ (G._*G_ (G._*G_ (a) (b)) (c)) (G.conjG (G._*G_ (G._*G_ (d) (e)) (f))))
  ≡ G._*G_ (G._*G_ (FFT.scaleG FFT.quarter (G._*G_ (a) (G.conjG d))) (FFT.scaleG FFT.quarter (G._*G_ (b) (G.conjG e)))) (FFT.scaleG FFT.quarter (G._*G_ (c) (G.conjG f)))
gaussianTripleNormalizedPhaseScale a b c d e f =
  let
    conjugateDistribution :
      G.conjG (G._*G_ (G._*G_ (d) (e)) (f))
      ≡ G._*G_ (G._*G_ (G.conjG d) (G.conjG e)) (G.conjG f)
    conjugateDistribution =
      trans
        (G.gaussianConjMul (G._*G_ (d) (e)) f)
        (cong (λ v → G._*G_ (v) (G.conjG f))
          (G.gaussianConjMul d e))

    rearrange :
      G._*G_ (G._*G_ (G._*G_ (a) (b)) (c)) (G._*G_ (G._*G_ (G.conjG d) (G.conjG e)) (G.conjG f))
      ≡ G._*G_ (G._*G_ (G._*G_ (a) (G.conjG d)) (G._*G_ (b) (G.conjG e))) (G._*G_ (c) (G.conjG f))
    rearrange =
      trans
        (Bilinear.productShuffle4 gaussianCoefficientOps gaussianFiniteSumAlgebra
          (G._*G_ (a) (b)) c
          (G._*G_ (G.conjG d) (G.conjG e)) (G.conjG f))
        (cong
          (λ v → G._*G_ (v) (G._*G_ (c) (G.conjG f)))
          (Bilinear.productShuffle4 gaussianCoefficientOps gaussianFiniteSumAlgebra
            a b (G.conjG d) (G.conjG e))))

    factorScale :
      FFT.scaleG norm64 (G._*G_ (G._*G_ (G._*G_ (a) (G.conjG d)) (G._*G_ (b) (G.conjG e))) (G._*G_ (c) (G.conjG f)))
      ≡ G._*G_ (G._*G_ (FFT.scaleG FFT.quarter (G._*G_ (a) (G.conjG d))) (FFT.scaleG FFT.quarter (G._*G_ (b) (G.conjG e)))) (FFT.scaleG FFT.quarter (G._*G_ (c) (G.conjG f)))
    factorScale =
      trans
        (cong
          (λ q → FFT.scaleG q (G._*G_ (G._*G_ (G._*G_ (a) (G.conjG d)) (G._*G_ (b) (G.conjG e))) (G._*G_ (c) (G.conjG f))))
          gaussianCubeScaleFactor)
        (trans
          (FFT.gaussianScaleOfProduct
            (FFT.quarter * FFT.quarter) FFT.quarter
            (G._*G_ (G._*G_ (a) (G.conjG d)) (G._*G_ (b) (G.conjG e))) (G._*G_ (c) (G.conjG f)))
          (cong
            (λ v → G._*G_ (v) (FFT.scaleG FFT.quarter (G._*G_ (c) (G.conjG f))))
            (FFT.gaussianScaleOfProduct FFT.quarter FFT.quarter
              (G._*G_ (a) (G.conjG d)) (G._*G_ (b) (G.conjG e)))))
  in
  trans
    (cong
      (λ v → FFT.scaleG norm64 (G._*G_ (G._*G_ (G._*G_ (a) (b)) (c)) (v)))
      conjugateDistribution)
    (trans
      (cong (λ v → FFT.scaleG norm64 v) rearrange)
      factorScale)


------------------------------------------------------------------------
-- DISCHARGED THREE-AXIS ORIGINAL SOURCE-ORDER CHARACTER RESOLUTION.
-- This is the exact 64-term Fourier delta, NOT the distinct actual
-- sampled-FFT array-identification payment.  Uses 16 original
-- one-axis cases, generic Fubini and Boolean triple selector.
------------------------------------------------------------------------

gaussianAxisNormalizedPhase :
  Four.FourGridMode → Four.FourGridMode →
  Four.FourGridMode → G.Gaussian4
gaussianAxisNormalizedPhase k l x =
  FFT.scaleG FFT.quarter
    (G._*G_ (G.character4 k x) (G.conjG (G.character4 l x)))

gaussianCubeNormalizedPhaseSplit :
  (k l x : Four.FourGridCube64) →
  FFT.scaleG norm64
    (G._*G_ (gaussianCubeCharacter k x)
      (G.conjG (gaussianCubeCharacter l x)))
  ≡ G._*G_
      (G._*G_
        (gaussianAxisNormalizedPhase
          (fourAxisX k) (fourAxisX l) (fourAxisX x))
        (gaussianAxisNormalizedPhase
          (fourAxisY k) (fourAxisY l) (fourAxisY x)))
      (gaussianAxisNormalizedPhase
        (fourAxisZ k) (fourAxisZ l) (fourAxisZ x))
  where
  fourAxisX : Four.FourGridCube64 → Four.FourGridMode
  fourAxisX (Four.fourCube a b c) = a
  fourAxisY : Four.FourGridCube64 → Four.FourGridMode
  fourAxisY (Four.fourCube a b c) = b
  fourAxisZ : Four.FourGridCube64 → Four.FourGridMode
  fourAxisZ (Four.fourCube a b c) = c
gaussianCubeNormalizedPhaseSplit
  (Four.fourCube a b c)
  (Four.fourCube d e f)
  (Four.fourCube x y z) =
  gaussianTripleNormalizedPhaseScale
    (G.character4 a x) (G.character4 b y) (G.character4 c z)
    (G.character4 d x) (G.character4 e y) (G.character4 f z)

gaussianActualCubeCharacterResolution :
  (k l : Four.FourGridCube64) →
  Bilinear.sumAll gaussianCoefficientOps Nyquist.allFourGridCubes
    (λ x → FFT.scaleG norm64
      (G._*G_ (gaussianCubeCharacter k x)
        (G.conjG (gaussianCubeCharacter l x))))
  ≡ Bilinear.choose G.zeroG (Four.eqFourCube k l) G.oneG
gaussianActualCubeCharacterResolution
  (Four.fourCube a b c) (Four.fourCube d e f) =
  trans
    (gaussianActualNyquistSeparableProduct
      (gaussianAxisNormalizedPhase a d)
      (gaussianAxisNormalizedPhase b e)
      (gaussianAxisNormalizedPhase c f)
      (λ cube → FFT.scaleG norm64
        (G._*G_
          (gaussianCubeCharacter (Four.fourCube a b c) cube)
          (G.conjG
            (gaussianCubeCharacter (Four.fourCube d e f) cube))))
      (gaussianCubeNormalizedPhaseSplit
        (Four.fourCube a b c) (Four.fourCube d e f)))
    (trans
      (cong₂ G._*G_
        (cong₂ G._*G_
          (gaussianOriginalAxisCharacterResolution a d)
          (gaussianOriginalAxisCharacterResolution b e))
        (gaussianOriginalAxisCharacterResolution c f))
      (Bilinear.sourceChooseProductTriple
        gaussianCoefficientOps gaussianFiniteSumAlgebra
        G.oneG (G.scalarMulOneRight G.oneG)
        (Four.eqFour a d)
        (Four.eqFour b e)
        (Four.eqFour c f)))
