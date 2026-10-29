module DASHI.Physics.Closure.R2P2C5FullSampledFourierBidiExact where

------------------------------------------------------------------------
-- FULL 5^3 GAUSSIAN-ANALOGUE FIVE-ROOT CYCLOTOMIC SAMPLE TRANSFORM.
-- Real base Q(zeta5), not Q(i), Q(omega), generic complex floats, zeta
-- functions or Monster representations. Original finite-group/cyclic
-- spectral mathematics and source Q(zeta5) character owner credited.
-- Source-written, Agda kernel pending.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _*_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
import DASHI.Physics.Closure.R2P2C5CyclotomicFullFourierCharacterExact as C5
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I

open C5 using (Cyclotomic5; cyc5; _+5_; _*5_; cyc5-ext)

record Quint (A : Set) : Set where
  constructor quint
  field t0 t1 t2 t3 t4 : A
open Quint public

mapQuint : ∀ {A B : Set} → (A → B) → Quint A → Quint B
mapQuint f (quint a b c d e) = quint (f a) (f b) (f c) (f d) (f e)

zipQuint :
  ∀ {A B C : Set} → (A → B → C) → Quint A → Quint B → Quint C
zipQuint f (quint a b c d e) (quint g h i j k) =
  quint (f a g) (f b h) (f c i) (f d j) (f e k)

quint-ext :
  ∀ {A : Set} {a b c d e f g h i j : A} →
  a ≡ f → b ≡ g → c ≡ h → d ≡ i → e ≡ j →
  quint a b c d e ≡ quint f g h i j
quint-ext refl refl refl refl refl = refl

quintFrom :
  ∀ {A : Set} → (I.FiveGridMode → A) → Quint A
quintFrom f =
  quint (f I.gridZero) (f I.gridPlusOne) (f I.gridPlusTwo)
        (f I.gridMinusTwo) (f I.gridMinusOne)

quintAt : ∀ {A : Set} → Quint A → I.FiveGridMode → A
quintAt (quint a b c d e) I.gridZero = a
quintAt (quint a b c d e) I.gridPlusOne = b
quintAt (quint a b c d e) I.gridPlusTwo = c
quintAt (quint a b c d e) I.gridMinusTwo = d
quintAt (quint a b c d e) I.gridMinusOne = e

quintSection :
  ∀ {A : Set} (f : I.FiveGridMode → A) (x : I.FiveGridMode) →
  quintAt (quintFrom f) x ≡ f x
quintSection f I.gridZero = refl
quintSection f I.gridPlusOne = refl
quintSection f I.gridPlusTwo = refl
quintSection f I.gridMinusTwo = refl
quintSection f I.gridMinusOne = refl

scale5 : ℚ → C5.Cyclotomic5 → C5.Cyclotomic5
scale5 q (cyc5 a b c d) =
  cyc5 (q * a) (q * b) (q * c) (q * d)

oneFifth : ℚ
oneFifth = normalize 1 5

forwardAt : I.FiveGridMode → Quint C5.Cyclotomic5 → C5.Cyclotomic5
forwardAt k v =
  C5.sum5 (λ x →
    C5._*5_ (quintAt v x) (C5.conj5 (C5.character5 k x)))

inverseAt : I.FiveGridMode → Quint C5.Cyclotomic5 → C5.Cyclotomic5
inverseAt x v =
  scale5 oneFifth
    (C5.sum5 (λ k → C5._*5_ (quintAt v k) (C5.character5 k x)))

forward1 : Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5
forward1 v = quintFrom (λ k → forwardAt k v)

inverse1 : Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5
inverse1 v = quintFrom (λ x → inverseAt x v)

-- Arbitrary input: 5 independently chosen Q(zeta5) entries.
-- Each entry has four rational coordinates, not just root powers.
oneDimensionalFourierInversion :
  (v : Quint C5.Cyclotomic5) → inverse1 (forward1 v) ≡ v
oneDimensionalFourierInversion
  (quint (cyc5 a0 a1 a2 a3)
         (cyc5 b0 b1 b2 b3)
         (cyc5 c0 c1 c2 c3)
         (cyc5 d0 d1 d2 d3)
         (cyc5 e0 e1 e2 e3)) =
  quint-ext
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)

oneDimensionalFourierForwardInverse :
  (v : Quint C5.Cyclotomic5) → forward1 (inverse1 v) ≡ v
oneDimensionalFourierForwardInverse
  (quint (cyc5 a0 a1 a2 a3)
         (cyc5 b0 b1 b2 b3)
         (cyc5 c0 c1 c2 c3)
         (cyc5 d0 d1 d2 d3)
         (cyc5 e0 e1 e2 e3)) =
  quint-ext
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)

CubeSignal125 : Set
CubeSignal125 = Quint (Quint (Quint C5.Cyclotomic5))

transpose5 : ∀ {A : Set} → Quint (Quint A) → Quint (Quint A)
transpose5 (quint
    (quint a00 a01 a02 a03 a04)
    (quint a10 a11 a12 a13 a14)
    (quint a20 a21 a22 a23 a24)
    (quint a30 a31 a32 a33 a34)
    (quint a40 a41 a42 a43 a44)) =
  quint
    (quint a00 a10 a20 a30 a40)
    (quint a01 a11 a21 a31 a41)
    (quint a02 a12 a22 a32 a42)
    (quint a03 a13 a23 a33 a43)
    (quint a04 a14 a24 a34 a44)

transpose5Involutive :
  ∀ {A : Set} (m : Quint (Quint A)) →
  transpose5 (transpose5 m) ≡ m
transpose5Involutive
  (quint (quint a b c d e) (quint f g h i j)
         (quint k l m n o) (quint p q r s t)
         (quint u v w x y)) = refl

mapQuintRoundTrip :
  ∀ {A : Set} (forward inverse : A → A) →
  ((x : A) → inverse (forward x) ≡ x) →
  (xs : Quint A) →
  mapQuint inverse (mapQuint forward xs) ≡ xs
mapQuintRoundTrip forward inverse proof (quint a b c d e)
  rewrite proof a | proof b | proof c | proof d | proof e = refl

transformZ : CubeSignal125 → CubeSignal125
transformZ = mapQuint (mapQuint forward1)

inverseZ : CubeSignal125 → CubeSignal125
inverseZ = mapQuint (mapQuint inverse1)

transformMatrixY : Quint (Quint C5.Cyclotomic5) → Quint (Quint C5.Cyclotomic5)
transformMatrixY m = transpose5 (mapQuint forward1 (transpose5 m))

inverseMatrixY : Quint (Quint C5.Cyclotomic5) → Quint (Quint C5.Cyclotomic5)
inverseMatrixY m = transpose5 (mapQuint inverse1 (transpose5 m))

transformY : CubeSignal125 → CubeSignal125
transformY = mapQuint transformMatrixY

inverseY : CubeSignal125 → CubeSignal125
inverseY = mapQuint inverseMatrixY

swapXY : CubeSignal125 → CubeSignal125
swapXY (quint
  (quint a00 a01 a02 a03 a04)
  (quint a10 a11 a12 a13 a14)
  (quint a20 a21 a22 a23 a24)
  (quint a30 a31 a32 a33 a34)
  (quint a40 a41 a42 a43 a44)
) = quint
  (quint a00 a10 a20 a30 a40)
  (quint a01 a11 a21 a31 a41)
  (quint a02 a12 a22 a32 a42)
  (quint a03 a13 a23 a33 a43)
  (quint a04 a14 a24 a34 a44)

swapXYInvolutive :
  (xs : CubeSignal125) → swapXY (swapXY xs) ≡ xs
swapXYInvolutive
  (quint (quint a b c d e) (quint f g h i j)
         (quint k l m n o) (quint p q r s t)
         (quint u v w x y)) = refl

transformX : CubeSignal125 → CubeSignal125
transformX xs = swapXY (transformY (swapXY xs))

inverseX : CubeSignal125 → CubeSignal125
inverseX xs = swapXY (inverseY (swapXY xs))

zRoundTrip : (xs : CubeSignal125) → inverseZ (transformZ xs) ≡ xs
zRoundTrip (quint a b c d e)
  rewrite mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion a
        | mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion b
        | mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion c
        | mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion d
        | mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion e = refl

zForwardInverse : (xs : CubeSignal125) → transformZ (inverseZ xs) ≡ xs
zForwardInverse (quint a b c d e)
  rewrite mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse a
        | mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse b
        | mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse c
        | mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse d
        | mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse e = refl

matrixYRoundTrip :
  (m : Quint (Quint C5.Cyclotomic5)) →
  inverseMatrixY (transformMatrixY m) ≡ m
matrixYRoundTrip m
  rewrite transpose5Involutive (mapQuint forward1 (transpose5 m))
        | mapQuintRoundTrip forward1 inverse1 oneDimensionalFourierInversion (transpose5 m)
        | transpose5Involutive m = refl

matrixYForwardInverse :
  (m : Quint (Quint C5.Cyclotomic5)) →
  transformMatrixY (inverseMatrixY m) ≡ m
matrixYForwardInverse m
  rewrite transpose5Involutive (mapQuint inverse1 (transpose5 m))
        | mapQuintRoundTrip inverse1 forward1 oneDimensionalFourierForwardInverse (transpose5 m)
        | transpose5Involutive m = refl

yRoundTrip : (xs : CubeSignal125) → inverseY (transformY xs) ≡ xs
yRoundTrip (quint a b c d e)
  rewrite matrixYRoundTrip a | matrixYRoundTrip b | matrixYRoundTrip c
        | matrixYRoundTrip d | matrixYRoundTrip e = refl

yForwardInverse : (xs : CubeSignal125) → transformY (inverseY xs) ≡ xs
yForwardInverse (quint a b c d e)
  rewrite matrixYForwardInverse a | matrixYForwardInverse b | matrixYForwardInverse c
        | matrixYForwardInverse d | matrixYForwardInverse e = refl

xRoundTrip : (xs : CubeSignal125) → inverseX (transformX xs) ≡ xs
xRoundTrip xs
  rewrite swapXYInvolutive (transformY (swapXY xs))
        | yRoundTrip (swapXY xs)
        | swapXYInvolutive xs = refl

xForwardInverse : (xs : CubeSignal125) → transformX (inverseX xs) ≡ xs
xForwardInverse xs
  rewrite swapXYInvolutive (inverseY (swapXY xs))
        | yForwardInverse (swapXY xs)
        | swapXYInvolutive xs = refl

fourier125 : CubeSignal125 → CubeSignal125
fourier125 xs = transformX (transformY (transformZ xs))

inverseFourier125 : CubeSignal125 → CubeSignal125
inverseFourier125 xs = inverseZ (inverseY (inverseX xs))

cubeFourierInversion :
  (xs : CubeSignal125) → inverseFourier125 (fourier125 xs) ≡ xs
cubeFourierInversion xs
  rewrite xRoundTrip (transformY (transformZ xs))
        | yRoundTrip (transformZ xs)
        | zRoundTrip xs = refl

cubeFourierForwardInverse :
  (xs : CubeSignal125) → fourier125 (inverseFourier125 xs) ≡ xs
cubeFourierForwardInverse xs
  rewrite zForwardInverse (inverseY (inverseX xs))
        | yForwardInverse (inverseX xs)
        | xForwardInverse xs = refl

pointwiseProduct125 : CubeSignal125 → CubeSignal125 → CubeSignal125
pointwiseProduct125 = zipQuint (zipQuint (zipQuint C5._*5_))

-- Source-written full 125-sample transform and pointwise product.
-- Exact padded 27->125 physical integer-frequency bilinear equality
-- remains a separate kernel obligation, not an axiom or claimed result.

------------------------------------------------------------------------
-- FULL C5 ONE-AXIS SAMPLED PRODUCT/CYCLIC CONVOLUTION LEMMA.
--
-- Reuses original fiveGroupAdd and source C5 inverse; this is NOT
-- an extra five-group presentation. Same Q(zeta5) coefficient carrier.
-- Normalised inverse1 means the forward transform of two synthesised
-- signals is 1/5 times cyclic convolution, so multiply by FIVE.
-- The three-axis 27/729 indexed map remains a separate proof boundary.
------------------------------------------------------------------------

import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P2C4C5NyquistAntipodalFixedPointExact as Nyquist

pointwiseProduct1 : Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5 →
  Quint C5.Cyclotomic5
pointwiseProduct1 = zipQuint C5._*5_

wholeFive : ℚ
wholeFive = normalize 5 1

scaleQuint : ℚ → Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5
scaleQuint q = mapQuint (scale5 q)

-- Reuse inherited ORIGINAL cyclic group addition and additive inverse.
cyclicConvolutionAt :
  I.FiveGridMode → Quint C5.Cyclotomic5 →
  Quint C5.Cyclotomic5 → C5.Cyclotomic5
cyclicConvolutionAt k a b =
  C5.sum5 λ p →
    C5._*5_ (quintAt a p)
      (quintAt b
        (Full.fiveGroupAdd k (Nyquist.fiveGroupAntipode p)))

cyclicConvolution5 :
  Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5 →
  Quint C5.Cyclotomic5
cyclicConvolution5 a b =
  quintFrom λ k → cyclicConvolutionAt k a b

sampledConvolution5 :
  Quint C5.Cyclotomic5 → Quint C5.Cyclotomic5 →
  Quint C5.Cyclotomic5
sampledConvolution5 a b =
  scaleQuint wholeFive
    (forward1 (pointwiseProduct1 (inverse1 a) (inverse1 b)))

-- Two INDEPENDENT arbitrary cyclotomic five-point coefficient fields.
-- Finite ring proof, not floating-point or an appeal to Fourier folklore.
-- The ring solver normalises over 40 independent rational coordinates.
oneAxisSampledConvolutionIsCyclic :
  (a b : Quint C5.Cyclotomic5) →
  sampledConvolution5 a b ≡ cyclicConvolution5 a b
oneAxisSampledConvolutionIsCyclic
  (quint (cyc5 a0 a1 a2 a3) (cyc5 b0 b1 b2 b3)
         (cyc5 c0 c1 c2 c3) (cyc5 d0 d1 d2 d3)
         (cyc5 e0 e1 e2 e3))
  (quint (cyc5 f0 f1 f2 f3) (cyc5 g0 g1 g2 g3)
         (cyc5 h0 h1 h2 h3) (cyc5 i0 i1 i2 i3)
         (cyc5 j0 j1 j2 j3)) =
  quint-ext
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)
    (cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀)

-- IMPORTANT: source-written Agda proof candidate; no executed kernel
-- check. The 125-sample three-axis sampled/index theorem is still open.
