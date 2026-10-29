module DASHI.Physics.Closure.R2P2C4GaussianSampledFourierBidiExact where

------------------------------------------------------------------------
-- C4 FOURIER FORWARD/INVERSE ON ACTUAL 4x4x4 SAMPLE ARRAYS
--
-- Source-owned precursor:
--   R2P2C4GaussianFourierCharacterExact (Q(i), C4 characters)
--   R2P227729FourGridRetainedQuadraticParetoExact (Z/4 group)
--   C3CubeCyclotomicFourierExact (inherited *method*, distinct Q(omega)).
--
-- This is a genuinely different four-point DFT from the source C3 FFT.
-- The forward transform is UNNORMALIZED; the inverse is divided by four
-- on each axis, hence by 64 on the cube. We do not assert its nonlinear
-- coefficient equals true integer convolution until the input padding,
-- output projection, and sampled multiplication bridge are proved.
-- Source written; no Agda kernel receipt. No NS/Monster/clock promotion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
import DASHI.Physics.Closure.R2P2C4GaussianFourierCharacterExact as C4

open C4 using (Gaussian4; gauss; zeroG; oneG; iG; negOneG; negIG;
               _+G_; _*G_; gauss-ext)

quarter : ℚ
quarter = normalize 1 4

scaleG : ℚ → Gaussian4 → Gaussian4
scaleG q (gauss a b) = gauss (q * a) (q * b)

record Quad (A : Set) : Set where
  constructor quad
  field t0 t1 t2 t3 : A
open Quad public

mapQuad : ∀ {A B} → (A → B) → Quad A → Quad B
mapQuad f (quad a b c d) = quad (f a) (f b) (f c) (f d)

zipQuad : ∀ {A B C} → (A → B → C) → Quad A → Quad B → Quad C
zipQuad f (quad a b c d) (quad e g h j) =
  quad (f a e) (f b g) (f c h) (f d j)

quad-ext :
  ∀ {A : Set} {a b c d e f g h : A} →
  a ≡ e → b ≡ f → c ≡ g → d ≡ h →
  quad a b c d ≡ quad e f g h
quad-ext refl refl refl refl = refl

-- The negative exponent convention in the unnormalized forward DFT:
--  k=1 row is [1,-i,-1,+i]; inverse uses conjugate rows / 4.
forward1 : Quad Gaussian4 → Quad Gaussian4
forward1 (quad a b c d) = quad
  (a +G b +G c +G d)
  (a +G (negIG *G b) +G (negOneG *G c) +G (iG *G d))
  (a +G (negOneG *G b) +G c +G (negOneG *G d))
  (a +G (iG *G b) +G (negOneG *G c) +G (negIG *G d))

inverse1 : Quad Gaussian4 → Quad Gaussian4
inverse1 (quad a b c d) = quad
  (scaleG quarter (a +G b +G c +G d))
  (scaleG quarter
    (a +G (iG *G b) +G (negOneG *G c) +G (negIG *G d)))
  (scaleG quarter
    (a +G (negOneG *G b) +G c +G (negOneG *G d)))
  (scaleG quarter
    (a +G (negIG *G b) +G (negOneG *G c) +G (iG *G d)))

-- Exact arbitrary Q(i) coefficients (eight independent rationals).
oneDimensionalFourierInversion :
  (x : Quad Gaussian4) → inverse1 (forward1 x) ≡ x
oneDimensionalFourierInversion
  (quad (gauss a0 a1) (gauss b0 b1)
        (gauss c0 c1) (gauss d0 d1)) =
  quad-ext (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)

oneDimensionalFourierForwardInverse :
  (x : Quad Gaussian4) → forward1 (inverse1 x) ≡ x
oneDimensionalFourierForwardInverse
  (quad (gauss a0 a1) (gauss b0 b1)
        (gauss c0 c1) (gauss d0 d1)) =
  quad-ext (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)

CubeSignal64 : Set
CubeSignal64 = Quad (Quad (Quad Gaussian4))

transpose4 : ∀ {A : Set} → Quad (Quad A) → Quad (Quad A)
transpose4
  (quad (quad a00 a01 a02 a03)
        (quad a10 a11 a12 a13)
        (quad a20 a21 a22 a23)
        (quad a30 a31 a32 a33)) =
  quad (quad a00 a10 a20 a30)
       (quad a01 a11 a21 a31)
       (quad a02 a12 a22 a32)
       (quad a03 a13 a23 a33)

transpose4Involutive :
  ∀ {A : Set} (m : Quad (Quad A)) →
  transpose4 (transpose4 m) ≡ m
transpose4Involutive
  (quad (quad a b c d) (quad e f g h)
        (quad i j k l) (quad m n o p)) = refl

mapQuadRoundTrip :
  ∀ {A : Set} (forward inverse : A → A) →
  ((x : A) → inverse (forward x) ≡ x) →
  (xs : Quad A) →
  mapQuad inverse (mapQuad forward xs) ≡ xs
mapQuadRoundTrip forward inverse proof (quad a b c d)
  rewrite proof a | proof b | proof c | proof d = refl

transformZ : CubeSignal64 → CubeSignal64
transformZ = mapQuad (mapQuad forward1)

inverseZ : CubeSignal64 → CubeSignal64
inverseZ = mapQuad (mapQuad inverse1)

transformMatrixY : Quad (Quad Gaussian4) → Quad (Quad Gaussian4)
transformMatrixY m = transpose4 (mapQuad forward1 (transpose4 m))

inverseMatrixY : Quad (Quad Gaussian4) → Quad (Quad Gaussian4)
inverseMatrixY m = transpose4 (mapQuad inverse1 (transpose4 m))

transformY : CubeSignal64 → CubeSignal64
transformY = mapQuad transformMatrixY

inverseY : CubeSignal64 → CubeSignal64
inverseY = mapQuad inverseMatrixY

swapXY : CubeSignal64 → CubeSignal64
swapXY (quad
  (quad x00 x01 x02 x03)
  (quad x10 x11 x12 x13)
  (quad x20 x21 x22 x23)
  (quad x30 x31 x32 x33)) =
  quad (quad x00 x10 x20 x30)
       (quad x01 x11 x21 x31)
       (quad x02 x12 x22 x32)
       (quad x03 x13 x23 x33)

swapXYInvolutive :
  (x : CubeSignal64) → swapXY (swapXY x) ≡ x
swapXYInvolutive
  (quad (quad a b c d) (quad e f g h)
        (quad i j k l) (quad m n o p)) = refl

transformX : CubeSignal64 → CubeSignal64
transformX x = swapXY (transformY (swapXY x))

inverseX : CubeSignal64 → CubeSignal64
inverseX x = swapXY (inverseY (swapXY x))

zRoundTrip : (x : CubeSignal64) → inverseZ (transformZ x) ≡ x
zRoundTrip (quad a b c d)
  rewrite mapQuadRoundTrip forward1 inverse1 oneDimensionalFourierInversion a
        | mapQuadRoundTrip forward1 inverse1 oneDimensionalFourierInversion b
        | mapQuadRoundTrip forward1 inverse1 oneDimensionalFourierInversion c
        | mapQuadRoundTrip forward1 inverse1 oneDimensionalFourierInversion d =
  refl

zForwardInverse : (x : CubeSignal64) → transformZ (inverseZ x) ≡ x
zForwardInverse (quad a b c d)
  rewrite mapQuadRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse a
        | mapQuadRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse b
        | mapQuadRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse c
        | mapQuadRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse d =
  refl

matrixYRoundTrip :
  (m : Quad (Quad Gaussian4)) →
  inverseMatrixY (transformMatrixY m) ≡ m
matrixYRoundTrip m
  rewrite transpose4Involutive (mapQuad forward1 (transpose4 m))
        | mapQuadRoundTrip forward1 inverse1
            oneDimensionalFourierInversion (transpose4 m)
        | transpose4Involutive m = refl

matrixYForwardInverse :
  (m : Quad (Quad Gaussian4)) →
  transformMatrixY (inverseMatrixY m) ≡ m
matrixYForwardInverse m
  rewrite transpose4Involutive (mapQuad inverse1 (transpose4 m))
        | mapQuadRoundTrip inverse1 forward1
            oneDimensionalFourierForwardInverse (transpose4 m)
        | transpose4Involutive m = refl

yRoundTrip : (x : CubeSignal64) → inverseY (transformY x) ≡ x
yRoundTrip (quad a b c d)
  rewrite matrixYRoundTrip a | matrixYRoundTrip b
        | matrixYRoundTrip c | matrixYRoundTrip d = refl

yForwardInverse : (x : CubeSignal64) → transformY (inverseY x) ≡ x
yForwardInverse (quad a b c d)
  rewrite matrixYForwardInverse a | matrixYForwardInverse b
        | matrixYForwardInverse c | matrixYForwardInverse d = refl

xRoundTrip : (x : CubeSignal64) → inverseX (transformX x) ≡ x
xRoundTrip x
  rewrite swapXYInvolutive (transformY (swapXY x))
        | yRoundTrip (swapXY x)
        | swapXYInvolutive x = refl

xForwardInverse : (x : CubeSignal64) → transformX (inverseX x) ≡ x
xForwardInverse x
  rewrite swapXYInvolutive (inverseY (swapXY x))
        | yForwardInverse (swapXY x)
        | swapXYInvolutive x = refl

fourier64 : CubeSignal64 → CubeSignal64
fourier64 x = transformX (transformY (transformZ x))

inverseFourier64 : CubeSignal64 → CubeSignal64
inverseFourier64 x = inverseZ (inverseY (inverseX x))

cubeFourierInversion :
  (x : CubeSignal64) → inverseFourier64 (fourier64 x) ≡ x
cubeFourierInversion x
  rewrite xRoundTrip (transformY (transformZ x))
        | yRoundTrip (transformZ x)
        | zRoundTrip x = refl

cubeFourierForwardInverse :
  (x : CubeSignal64) → fourier64 (inverseFourier64 x) ≡ x
cubeFourierForwardInverse x
  rewrite zForwardInverse (inverseY (inverseX x))
        | yForwardInverse (inverseX x)
        | xForwardInverse x = refl

-- A true sampled pointwise operator with the 64 actual Q(i) samples.
pointwiseProduct64 : CubeSignal64 → CubeSignal64 → CubeSignal64
pointwiseProduct64 = zipQuad (zipQuad (zipQuad C4._*G_))

-- Coefficients on the RIGHT are spectral (unnormalized forward DFT);
-- inverseFourier64 synthesizes sampled values with 1/64 normalization.
-- For the conventional unnormalized synthesis U(x)=Σ_k u_k χ_k(x),
-- supply 64*u as the Fourier input, rather than assuming inverse64
-- already has that normalization.
spectralSampledProduct64 :
  CubeSignal64 → CubeSignal64 → CubeSignal64
spectralSampledProduct64 f g =
  fourier64
    (pointwiseProduct64 (inverseFourier64 f) (inverseFourier64 g))

-- This typed sampled multiplication now exists; the correct identity
-- is F((F^-1 f)(F^-1 g)) = (1/64) cyclic convolution(f,g).
-- The finite 27-mode zero-padding and physical Leray bridge remain
-- independent proof obligations.


------------------------------------------------------------------------
-- HIGHEST-ALPHA EXACT C4 ONE-AXIS SAMPLED MULTIPLICATION / CONVOLUTION.
-- This is the first distributive Fourier coefficient theorem, not only
-- forward/inverse roundtrip. It uses the original Q(i) root algebra and
-- the standard C4 group convolution, not an asserted FFT axiom.
------------------------------------------------------------------------

pointwiseProduct1 : Quad Gaussian4 → Quad Gaussian4 → Quad Gaussian4
pointwiseProduct1 = zipQuad _*G_

fourRational : ℚ
fourRational = 4

scaleQuad : ℚ → Quad Gaussian4 → Quad Gaussian4
scaleQuad q = mapQuad (scaleG q)

-- On arbitrary 4+4 coefficient entries the circular group convolution
-- is the four signed-residue interactions p+q=k (mod 4).
cyclicConvolution4 : Quad Gaussian4 → Quad Gaussian4 → Quad Gaussian4
cyclicConvolution4
  (quad a b c d) (quad e f g h) = quad
  (a *G e +G b *G h +G c *G g +G d *G f)
  (a *G f +G b *G e +G c *G h +G d *G g)
  (a *G g +G b *G f +G c *G e +G d *G h)
  (a *G h +G b *G g +G c *G f +G d *G e)

-- Since inverse1 includes a 1/4 factor, the Fourier transform of
-- products of inverse-synthesized samples is 1/4 of this convolution.
-- Thus the fourRational factor below is REQUIRED, not ornamental.
sampledConvolution4 :
  Quad Gaussian4 → Quad Gaussian4 → Quad Gaussian4
sampledConvolution4 a b =
  scaleQuad fourRational
    (forward1 (pointwiseProduct1 (inverse1 a) (inverse1 b)))

oneAxisSampledConvolutionIsCyclic :
  (a b : Quad Gaussian4) →
  sampledConvolution4 a b ≡ cyclicConvolution4 a b
oneAxisSampledConvolutionIsCyclic
  (quad (gauss a0 a1) (gauss b0 b1)
        (gauss c0 c1) (gauss d0 d1))
  (quad (gauss e0 e1) (gauss f0 f1)
        (gauss g0 g1) (gauss h0 h1)) =
  quad-ext (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)
           (gauss-ext solve-∀ solve-∀)

-- No claim that this 1D law by itself proves the padded 3D truncated
-- convolution. Tensor-distribution, support reindexing and the 27/729
-- target link are independent, still-visible kernel obligations.
