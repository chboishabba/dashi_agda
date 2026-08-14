module DASHI.Biology.Physical.C3CubeCyclotomicFourierExact where

------------------------------------------------------------------------
-- Exact cyclotomic Fourier closure for C3 and C3^3.
--
-- Scalars are Q(omega) represented in the basis 1,omega with
-- omega^2 + omega + 1 = 0.  No floating complex numbers or analytic limits are
-- involved.  A one-dimensional three-point DFT is proved invertible, then
-- tensorized across three axes, yielding an exact transform/inverse pair for
-- arbitrary 27-value signals on C3^3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

Phase : Set
Phase = Wheel.DepthWheelPhase

------------------------------------------------------------------------
-- Q(omega), omega^2 = -1-omega.
------------------------------------------------------------------------

record Cyclotomic3 : Set where
  constructor cyc
  field
    realPart omegaPart : ℚ

open Cyclotomic3 public

zeroC oneC omega omega2 : Cyclotomic3
zeroC = cyc 0ℚ 0ℚ
oneC  = cyc 1ℚ 0ℚ
omega = cyc 0ℚ 1ℚ
omega2 = cyc (- 1ℚ) (- 1ℚ)

infixl 6 _+C_
infixl 7 _*C_

_+C_ : Cyclotomic3 → Cyclotomic3 → Cyclotomic3
cyc a b +C cyc c d = cyc (a + c) (b + d)

_*C_ : Cyclotomic3 → Cyclotomic3 → Cyclotomic3
cyc a b *C cyc c d =
  cyc (a * c - b * d) (a * d + b * c - b * d)

negC : Cyclotomic3 → Cyclotomic3
negC (cyc a b) = cyc (- a) (- b)

conjC : Cyclotomic3 → Cyclotomic3
conjC (cyc a b) = cyc (a - b) (- b)

scaleC : ℚ → Cyclotomic3 → Cyclotomic3
scaleC q (cyc a b) = cyc (q * a) (q * b)

cyc-ext : ∀ {a b c d} → a ≡ c → b ≡ d → cyc a b ≡ cyc c d
cyc-ext refl refl = refl

omegaSquared : omega *C omega ≡ omega2
omegaSquared = cyc-ext solve-∀ solve-∀

cyclotomicPolynomial : oneC +C omega +C omega2 ≡ zeroC
cyclotomicPolynomial = cyc-ext solve-∀ solve-∀

mulAssociative : (x y z : Cyclotomic3) →
  (x *C y) *C z ≡ x *C (y *C z)
mulAssociative (cyc a b) (cyc c d) (cyc e f) =
  cyc-ext solve-∀ solve-∀

mulCommutative : (x y : Cyclotomic3) → x *C y ≡ y *C x
mulCommutative (cyc a b) (cyc c d) = cyc-ext solve-∀ solve-∀

mulOneRight : (x : Cyclotomic3) → x *C oneC ≡ x
mulOneRight (cyc a b) = cyc-ext solve-∀ solve-∀

mulOneLeft : (x : Cyclotomic3) → oneC *C x ≡ x
mulOneLeft (cyc a b) = cyc-ext solve-∀ solve-∀

conjugationInvolutive : (x : Cyclotomic3) → conjC (conjC x) ≡ x
conjugationInvolutive (cyc a b) = cyc-ext solve-∀ solve-∀

conjugationMultiplicative : (x y : Cyclotomic3) →
  conjC (x *C y) ≡ conjC x *C conjC y
conjugationMultiplicative (cyc a b) (cyc c d) = cyc-ext solve-∀ solve-∀

------------------------------------------------------------------------
-- Roots of unity and one-dimensional character orthogonality.
------------------------------------------------------------------------

root : Phase → Cyclotomic3
root Wheel.phase-0 = oneC
root Wheel.phase-1 = omega
root Wheel.phase-2 = omega2

rootConjugate : Phase → Cyclotomic3
rootConjugate x = conjC (root x)

rootCharacterHomomorphism : (x y : Phase) →
  root (Cube.add x y) ≡ root x *C root y
rootCharacterHomomorphism Wheel.phase-0 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-0 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-0 Wheel.phase-2 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-1 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-1 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-1 Wheel.phase-2 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-2 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-2 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
rootCharacterHomomorphism Wheel.phase-2 Wheel.phase-2 = cyc-ext solve-∀ solve-∀

sum3 : (Phase → Cyclotomic3) → Cyclotomic3
sum3 f = f Wheel.phase-0 +C f Wheel.phase-1 +C f Wheel.phase-2

character1 : Phase → Phase → Cyclotomic3
character1 k x = root (Cube.scalarCharacter k x)

inner1 : Phase → Phase → Cyclotomic3
inner1 k l =
  sum3 λ x → character1 k x *C conjC (character1 l x)

threeC : Cyclotomic3
threeC = cyc (1ℚ + 1ℚ + 1ℚ) 0ℚ

delta3 : Phase → Phase → Cyclotomic3
delta3 Wheel.phase-0 Wheel.phase-0 = threeC
delta3 Wheel.phase-0 Wheel.phase-1 = zeroC
delta3 Wheel.phase-0 Wheel.phase-2 = zeroC
delta3 Wheel.phase-1 Wheel.phase-0 = zeroC
delta3 Wheel.phase-1 Wheel.phase-1 = threeC
delta3 Wheel.phase-1 Wheel.phase-2 = zeroC
delta3 Wheel.phase-2 Wheel.phase-0 = zeroC
delta3 Wheel.phase-2 Wheel.phase-1 = zeroC
delta3 Wheel.phase-2 Wheel.phase-2 = threeC

oneDimensionalCharacterOrthogonality : (k l : Phase) →
  inner1 k l ≡ delta3 k l
oneDimensionalCharacterOrthogonality Wheel.phase-0 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-0 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-0 Wheel.phase-2 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-1 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-1 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-1 Wheel.phase-2 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-2 Wheel.phase-0 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-2 Wheel.phase-1 = cyc-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Wheel.phase-2 Wheel.phase-2 = cyc-ext solve-∀ solve-∀

------------------------------------------------------------------------
-- Product orthogonality.  Because the C3^3 characters are tensor products,
-- their 27-term inner sum factors into three exact one-dimensional sums.
------------------------------------------------------------------------

cubeInner : Cube.Cube3 → Cube.Cube3 → Cyclotomic3
cubeInner (Cube.cube3 kx ky kz) (Cube.cube3 lx ly lz) =
  inner1 kx lx *C inner1 ky ly *C inner1 kz lz

cubeDelta : Cube.Cube3 → Cube.Cube3 → Cyclotomic3
cubeDelta (Cube.cube3 kx ky kz) (Cube.cube3 lx ly lz) =
  delta3 kx lx *C delta3 ky ly *C delta3 kz lz

cubeCharacterOrthogonality : (k l : Cube.Cube3) →
  cubeInner k l ≡ cubeDelta k l
cubeCharacterOrthogonality (Cube.cube3 kx ky kz) (Cube.cube3 lx ly lz)
  rewrite oneDimensionalCharacterOrthogonality kx lx
        | oneDimensionalCharacterOrthogonality ky ly
        | oneDimensionalCharacterOrthogonality kz lz = refl

selfInnerIs27 :
  cubeInner
    (Cube.cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-1)
    (Cube.cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-1)
  ≡ cyc 27 0ℚ
selfInnerIs27 = cyc-ext solve-∀ solve-∀

distinctCharactersOrthogonal :
  cubeInner
    (Cube.cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-0)
    (Cube.cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-0)
  ≡ zeroC
distinctCharactersOrthogonal = cyc-ext solve-∀ solve-∀

------------------------------------------------------------------------
-- Exact one-dimensional DFT over Q(omega).
------------------------------------------------------------------------

record Triple (A : Set) : Set where
  constructor triple
  field t0 t1 t2 : A

open Triple public

mapTriple : ∀ {A B} → (A → B) → Triple A → Triple B
mapTriple f (triple a b c) = triple (f a) (f b) (f c)

triple-ext : ∀ {A} {a b c d e f : A} →
  a ≡ d → b ≡ e → c ≡ f →
  triple a b c ≡ triple d e f
triple-ext refl refl refl = refl

third : ℚ
third = normalize 1 3

forward1 : Triple Cyclotomic3 → Triple Cyclotomic3
forward1 (triple a b c) = triple
  (a +C b +C c)
  (a +C (omega2 *C b) +C (omega *C c))
  (a +C (omega *C b) +C (omega2 *C c))

inverse1 : Triple Cyclotomic3 → Triple Cyclotomic3
inverse1 (triple a b c) = triple
  (scaleC third (a +C b +C c))
  (scaleC third (a +C (omega *C b) +C (omega2 *C c)))
  (scaleC third (a +C (omega2 *C b) +C (omega *C c)))

oneDimensionalFourierInversion : (f : Triple Cyclotomic3) →
  inverse1 (forward1 f) ≡ f
oneDimensionalFourierInversion
  (triple (cyc a0 a1) (cyc b0 b1) (cyc c0 c1)) =
  triple-ext
    (cyc-ext solve-∀ solve-∀)
    (cyc-ext solve-∀ solve-∀)
    (cyc-ext solve-∀ solve-∀)

------------------------------------------------------------------------
-- Tensor the exact DFT across three axes.  This represents arbitrary
-- 3*3*3=27-value signals, not only separable/simple-tensor signals.
------------------------------------------------------------------------

CubeSignal : Set
CubeSignal = Triple (Triple (Triple Cyclotomic3))

transpose2 : ∀ {A} → Triple (Triple A) → Triple (Triple A)
transpose2 (triple
  (triple a00 a01 a02)
  (triple a10 a11 a12)
  (triple a20 a21 a22)) =
  triple
    (triple a00 a10 a20)
    (triple a01 a11 a21)
    (triple a02 a12 a22)

transpose2Involutive : ∀ {A} (m : Triple (Triple A)) →
  transpose2 (transpose2 m) ≡ m
transpose2Involutive
  (triple (triple a b c) (triple d e f) (triple g h i)) = refl

mapTripleRoundTrip : ∀ {A} (forward inverse : A → A) →
  ((x : A) → inverse (forward x) ≡ x) →
  (xs : Triple A) →
  mapTriple inverse (mapTriple forward xs) ≡ xs
mapTripleRoundTrip forward inverse p (triple a b c)
  rewrite p a | p b | p c = refl

transformZ : CubeSignal → CubeSignal
transformZ = mapTriple (mapTriple forward1)

inverseZ : CubeSignal → CubeSignal
inverseZ = mapTriple (mapTriple inverse1)

transformMatrixY : Triple (Triple Cyclotomic3) → Triple (Triple Cyclotomic3)
transformMatrixY m = transpose2 (mapTriple forward1 (transpose2 m))

inverseMatrixY : Triple (Triple Cyclotomic3) → Triple (Triple Cyclotomic3)
inverseMatrixY m = transpose2 (mapTriple inverse1 (transpose2 m))

transformY : CubeSignal → CubeSignal
transformY = mapTriple transformMatrixY

inverseY : CubeSignal → CubeSignal
inverseY = mapTriple inverseMatrixY

swapXY : CubeSignal → CubeSignal
swapXY (triple x0 x1 x2) =
  let m0 = transpose2 (triple (t0 x0) (t0 x1) (t0 x2))
      m1 = transpose2 (triple (t1 x0) (t1 x1) (t1 x2))
      m2 = transpose2 (triple (t2 x0) (t2 x1) (t2 x2))
  in triple (triple (t0 m0) (t0 m1) (t0 m2))
            (triple (t1 m0) (t1 m1) (t1 m2))
            (triple (t2 m0) (t2 m1) (t2 m2))

-- The explicit coordinate definition above is intentionally replaced below by
-- a simpler involutive x/y swap, written directly to keep elaboration small.
swapXYDirect : CubeSignal → CubeSignal
swapXYDirect
  (triple
    (triple x00 x01 x02)
    (triple x10 x11 x12)
    (triple x20 x21 x22)) =
  triple
    (triple x00 x10 x20)
    (triple x01 x11 x21)
    (triple x02 x12 x22)

swapXYInvolutive : (x : CubeSignal) → swapXYDirect (swapXYDirect x) ≡ x
swapXYInvolutive
  (triple
    (triple x00 x01 x02)
    (triple x10 x11 x12)
    (triple x20 x21 x22)) = refl

transformX : CubeSignal → CubeSignal
transformX x = swapXYDirect (transformY (swapXYDirect x))

inverseX : CubeSignal → CubeSignal
inverseX x = swapXYDirect (inverseY (swapXYDirect x))

zRoundTrip : (x : CubeSignal) → inverseZ (transformZ x) ≡ x
zRoundTrip (triple a b c)
  rewrite mapTripleRoundTrip forward1 inverse1 oneDimensionalFourierInversion a
        | mapTripleRoundTrip forward1 inverse1 oneDimensionalFourierInversion b
        | mapTripleRoundTrip forward1 inverse1 oneDimensionalFourierInversion c = refl

matrixYRoundTrip : (m : Triple (Triple Cyclotomic3)) →
  inverseMatrixY (transformMatrixY m) ≡ m
matrixYRoundTrip m
  rewrite transpose2Involutive m
        | mapTripleRoundTrip forward1 inverse1 oneDimensionalFourierInversion (transpose2 m)
        | transpose2Involutive m = refl

yRoundTrip : (x : CubeSignal) → inverseY (transformY x) ≡ x
yRoundTrip (triple a b c)
  rewrite matrixYRoundTrip a | matrixYRoundTrip b | matrixYRoundTrip c = refl

xRoundTrip : (x : CubeSignal) → inverseX (transformX x) ≡ x
xRoundTrip x
  rewrite swapXYInvolutive x
        | yRoundTrip (swapXYDirect x)
        | swapXYInvolutive x = refl

fourier27 : CubeSignal → CubeSignal
fourier27 x = transformX (transformY (transformZ x))

inverseFourier27 : CubeSignal → CubeSignal
inverseFourier27 x = inverseZ (inverseY (inverseX x))

cubeFourierInversion : (f : CubeSignal) →
  inverseFourier27 (fourier27 f) ≡ f
cubeFourierInversion f
  rewrite xRoundTrip (transformY (transformZ f))
        | yRoundTrip (transformZ f)
        | zRoundTrip f = refl

------------------------------------------------------------------------
-- Convolution theorem interface.  The exact DFT now exists; convolution on
-- CubeSignal is kept as the next algebraic owner rather than smuggling an
-- unproved 27-term indexing implementation into this theorem.
------------------------------------------------------------------------

record ConvolutionDiagonalisation : Set₁ where
  field
    convolution : CubeSignal → CubeSignal → CubeSignal
    pointwiseProduct : CubeSignal → CubeSignal → CubeSignal
    convolutionTheorem : (f g : CubeSignal) →
      fourier27 (convolution f g) ≡ pointwiseProduct (fourier27 f) (fourier27 g)

record FourierAuthorityBoundary : Set where
  field
    cyclotomicTransformIsFloatingComplexFFT : Bool
    cyclotomicTransformIsFloatingComplexFFTIsFalse :
      cyclotomicTransformIsFloatingComplexFFT ≡ false
    convolutionDiagonalisationAlreadyProved : Bool
    convolutionDiagonalisationAlreadyProvedIsFalse :
      convolutionDiagonalisationAlreadyProved ≡ false

canonicalFourierAuthorityBoundary : FourierAuthorityBoundary
canonicalFourierAuthorityBoundary = record
  { cyclotomicTransformIsFloatingComplexFFT = false
  ; cyclotomicTransformIsFloatingComplexFFTIsFalse = refl
  ; convolutionDiagonalisationAlreadyProved = false
  ; convolutionDiagonalisationAlreadyProvedIsFalse = refl
  }
