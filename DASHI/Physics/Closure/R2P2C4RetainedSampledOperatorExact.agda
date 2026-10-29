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
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
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
