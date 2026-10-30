module DASHI.Physics.Closure.R2P2C5CyclotomicFullFourierCharacterExact where

------------------------------------------------------------------------
-- FULL FIVE-POINT ROOT-OF-UNITY CHARACTER LAYER ON ORIGINAL C5^3.
--
-- Original index owner:
--   R2P227729FiniteQuadraticConvolutionExact, fiveGroupAdd.
-- Historical mathematical attribution: roots of unity, cyclic Fourier
-- characters, Patterson/Orszag pseudo-spectral dealiasing; Lambert,
-- Reneuve and Augier (2026) contemporary comparative analysis.
--
-- NEW exact coefficient carrier Q(zeta_5) in basis 1,z,z²,z³,
-- using Phi_5(z)=1+z+z²+z³+z⁴=0 and z^5=1. This is NOT the
-- unrelated arithmetic zeta function, C3 Q(omega), Monster action,
-- or a physical measurement. A true C5 sampled multiplication
-- operator is separate. Kernel execution pending.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full

record Cyclotomic5 : Set where
  constructor cyc5
  field q0 q1 q2 q3 : ℚ
open Cyclotomic5 public

zero5 one5 zeta5 : Cyclotomic5
zero5 = cyc5 0ℚ 0ℚ 0ℚ 0ℚ
one5 = cyc5 1ℚ 0ℚ 0ℚ 0ℚ
zeta5 = cyc5 0ℚ 1ℚ 0ℚ 0ℚ

infixl 6 _+5_
infixl 7 _*5_

_+5_ : Cyclotomic5 → Cyclotomic5 → Cyclotomic5
cyc5 a b c d +5 cyc5 e f g h =
  cyc5 (a + e) (b + f) (c + g) (d + h)

-- Five cyclic coefficients S0..S4 from 16 products. Relation z^4=-(1+z+z²+z³)
-- reduces each output coordinate to Si-S4. The z^5 and z^6
-- contributions are correctly returned to S0 and S1.
_*5_ : Cyclotomic5 → Cyclotomic5 → Cyclotomic5
cyc5 a b c d *5 cyc5 e f g h =
  let
    s0 = a * e + c * h + d * g
    s1 = a * f + b * e + d * h
    s2 = a * g + b * f + c * e
    s3 = a * h + b * g + c * f + d * e
    s4 = b * h + c * g + d * f
  in cyc5 (s0 - s4) (s1 - s4) (s2 - s4) (s3 - s4)

conj5 : Cyclotomic5 → Cyclotomic5
conj5 (cyc5 a b c d) =
  cyc5 (a - b) (- b) (d - b) (c - b)

cyc5-ext :
  ∀ {a b c d e f g h : ℚ} →
  a ≡ e → b ≡ f → c ≡ g → d ≡ h →
  cyc5 a b c d ≡ cyc5 e f g h
cyc5-ext refl refl refl refl = refl

zetaSquared : Cyclotomic5
zetaSquared = cyc5 0ℚ 0ℚ 1ℚ 0ℚ

zetaCubed : Cyclotomic5
zetaCubed = cyc5 0ℚ 0ℚ 0ℚ 1ℚ

zetaFourth : Cyclotomic5
zetaFourth = cyc5 (- 1ℚ) (- 1ℚ) (- 1ℚ) (- 1ℚ)

zetaSquaredLaw : zeta5 *5 zeta5 ≡ zetaSquared
zetaSquaredLaw = refl

zetaFourthLaw : zetaSquared *5 zetaSquared ≡ zetaFourth
zetaFourthLaw = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

zetaFifthLaw : zetaFourth *5 zeta5 ≡ one5
zetaFifthLaw = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

conjugationInvolutive :
  (x : Cyclotomic5) → conj5 (conj5 x) ≡ x
conjugationInvolutive (cyc5 a b c d) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

conjugationMultiplicative :
  (x y : Cyclotomic5) → conj5 (x *5 y) ≡ conj5 x *5 conj5 y
conjugationMultiplicative
  (cyc5 a b c d) (cyc5 e f g h) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

root5 : I.FiveGridMode → Cyclotomic5
root5 I.gridZero = one5
root5 I.gridPlusOne = zeta5
root5 I.gridPlusTwo = zetaSquared
root5 I.gridMinusTwo = zetaCubed
root5 I.gridMinusOne = zetaFourth

-- Multiplication of exponent residues, distinct from original
-- additive group operation, enumerated on the SAME 5-point carrier.
scalarProduct5 : I.FiveGridMode → I.FiveGridMode → I.FiveGridMode
scalarProduct5 I.gridZero I.gridZero = I.gridZero
scalarProduct5 I.gridZero I.gridPlusOne = I.gridZero
scalarProduct5 I.gridZero I.gridPlusTwo = I.gridZero
scalarProduct5 I.gridZero I.gridMinusTwo = I.gridZero
scalarProduct5 I.gridZero I.gridMinusOne = I.gridZero
scalarProduct5 I.gridPlusOne I.gridZero = I.gridZero
scalarProduct5 I.gridPlusOne I.gridPlusOne = I.gridPlusOne
scalarProduct5 I.gridPlusOne I.gridPlusTwo = I.gridPlusTwo
scalarProduct5 I.gridPlusOne I.gridMinusTwo = I.gridMinusTwo
scalarProduct5 I.gridPlusOne I.gridMinusOne = I.gridMinusOne
scalarProduct5 I.gridPlusTwo I.gridZero = I.gridZero
scalarProduct5 I.gridPlusTwo I.gridPlusOne = I.gridPlusTwo
scalarProduct5 I.gridPlusTwo I.gridPlusTwo = I.gridMinusOne
scalarProduct5 I.gridPlusTwo I.gridMinusTwo = I.gridPlusOne
scalarProduct5 I.gridPlusTwo I.gridMinusOne = I.gridMinusTwo
scalarProduct5 I.gridMinusTwo I.gridZero = I.gridZero
scalarProduct5 I.gridMinusTwo I.gridPlusOne = I.gridMinusTwo
scalarProduct5 I.gridMinusTwo I.gridPlusTwo = I.gridPlusOne
scalarProduct5 I.gridMinusTwo I.gridMinusTwo = I.gridMinusOne
scalarProduct5 I.gridMinusTwo I.gridMinusOne = I.gridPlusTwo
scalarProduct5 I.gridMinusOne I.gridZero = I.gridZero
scalarProduct5 I.gridMinusOne I.gridPlusOne = I.gridMinusOne
scalarProduct5 I.gridMinusOne I.gridPlusTwo = I.gridMinusTwo
scalarProduct5 I.gridMinusOne I.gridMinusTwo = I.gridPlusTwo
scalarProduct5 I.gridMinusOne I.gridMinusOne = I.gridPlusOne

rootGroupLaw :
  (a b : I.FiveGridMode) →
  root5 (Full.fiveGroupAdd a b) ≡ root5 a *5 root5 b
rootGroupLaw I.gridZero I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridZero I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridZero I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridZero I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridZero I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusOne I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusOne I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusOne I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusOne I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusOne I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusTwo I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusTwo I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusTwo I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusTwo I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridPlusTwo I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusTwo I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusTwo I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusTwo I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusTwo I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusTwo I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusOne I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusOne I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusOne I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusOne I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
rootGroupLaw I.gridMinusOne I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

character5 : I.FiveGridMode → I.FiveGridMode → Cyclotomic5
character5 k x = root5 (scalarProduct5 k x)

sum5 : (I.FiveGridMode → Cyclotomic5) → Cyclotomic5
sum5 f =
  f I.gridZero +5 f I.gridPlusOne +5 f I.gridPlusTwo +5
  f I.gridMinusTwo +5 f I.gridMinusOne

inner5 : I.FiveGridMode → I.FiveGridMode → Cyclotomic5
inner5 k l = sum5 λ x → character5 k x *5 conj5 (character5 l x)

eq5 : I.FiveGridMode → I.FiveGridMode → Bool
eq5 I.gridZero I.gridZero = true
eq5 I.gridPlusOne I.gridPlusOne = true
eq5 I.gridPlusTwo I.gridPlusTwo = true
eq5 I.gridMinusTwo I.gridMinusTwo = true
eq5 I.gridMinusOne I.gridMinusOne = true
eq5 _ _ = false

fiveScalar : Cyclotomic5
fiveScalar = cyc5 (1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ) 0ℚ 0ℚ 0ℚ

delta5 : I.FiveGridMode → I.FiveGridMode → Cyclotomic5
delta5 k l with eq5 k l
... | true = fiveScalar
... | false = zero5

oneDimensionalCharacterOrthogonality :
  (k l : I.FiveGridMode) → inner5 k l ≡ delta5 k l
oneDimensionalCharacterOrthogonality I.gridZero I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridZero I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridZero I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridZero I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridZero I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusOne I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusOne I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusOne I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusOne I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusOne I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusTwo I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusTwo I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusTwo I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusTwo I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridPlusTwo I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusTwo I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusTwo I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusTwo I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusTwo I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusTwo I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusOne I.gridZero = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusOne I.gridPlusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusOne I.gridPlusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusOne I.gridMinusTwo = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀
oneDimensionalCharacterOrthogonality I.gridMinusOne I.gridMinusOne = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

-- Three axes give exactly 125 independent samples; the only
-- self-negative full C5^3 frequency is the zero mode.
cubeInner5 : Full.GridCube125 → Full.GridCube125 → Cyclotomic5
cubeInner5 (Full.gridCube a b c) (Full.gridCube d e f) =
  inner5 a d *5 inner5 b e *5 inner5 c f

cubeDelta5 : Full.GridCube125 → Full.GridCube125 → Cyclotomic5
cubeDelta5 (Full.gridCube a b c) (Full.gridCube d e f) =
  delta5 a d *5 delta5 b e *5 delta5 c f

cubeCharacterOrthogonality :
  (k l : Full.GridCube125) →
  cubeInner5 k l ≡ cubeDelta5 k l
cubeCharacterOrthogonality (Full.gridCube a b c) (Full.gridCube d e f)
  rewrite oneDimensionalCharacterOrthogonality a d
        | oneDimensionalCharacterOrthogonality b e
        | oneDimensionalCharacterOrthogonality c f = refl

-- Unfinished separate owner: 5-point forward/inverse sampled transform
-- and tensorized full 125-output multiplication theorem.


------------------------------------------------------------------------
-- EXACT SCALAR RING LAWS FOR THE REPOSITORY-OWNED FINITE DFT.
-- Needed for distributing sampled pointwise products through nested
-- C4/C5 axis sums; they MUST precede any tensor convolution claim.
-- Proofs are in the ORIGINAL Q(i)/Q(zeta5) scalar carriers, not ℚ
-- coerced via an unproved equivalence. Source-written, kernel pending.
------------------------------------------------------------------------

scalarAddAssociative :
  (x y z : Cyclotomic5) →
  _+5_ (_+5_ x y) z ≡ _+5_ x (_+5_ y z)
scalarAddAssociative (cyc5 a b c d) (cyc5 e f g h) (cyc5 i j k l) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarAddCommutative :
  (x y : Cyclotomic5) → _+5_ x y ≡ _+5_ y x
scalarAddCommutative (cyc5 a b c d) (cyc5 e f g h) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarAddZeroLeft :
  (x : Cyclotomic5) → _+5_ zero5 x ≡ x
scalarAddZeroLeft (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarAddZeroRight :
  (x : Cyclotomic5) → _+5_ x zero5 ≡ x
scalarAddZeroRight (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulAssociative :
  (x y z : Cyclotomic5) →
  _*5_ (_*5_ x y) z ≡ _*5_ x (_*5_ y z)
scalarMulAssociative (cyc5 a b c d) (cyc5 e f g h) (cyc5 i j k l) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulCommutative :
  (x y : Cyclotomic5) → _*5_ x y ≡ _*5_ y x
scalarMulCommutative (cyc5 a b c d) (cyc5 e f g h) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulOneLeft :
  (x : Cyclotomic5) → _*5_ one5 x ≡ x
scalarMulOneLeft (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulOneRight :
  (x : Cyclotomic5) → _*5_ x one5 ≡ x
scalarMulOneRight (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulZeroLeft :
  (x : Cyclotomic5) → _*5_ zero5 x ≡ zero5
scalarMulZeroLeft (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulZeroRight :
  (x : Cyclotomic5) → _*5_ x zero5 ≡ zero5
scalarMulZeroRight (cyc5 a b c d) = cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulDistributesRight :
  (x y z : Cyclotomic5) →
  _*5_ (_+5_ x y) z ≡ _+5_ (_*5_ x z) (_*5_ y z)
scalarMulDistributesRight (cyc5 a b c d) (cyc5 e f g h) (cyc5 i j k l) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

scalarMulDistributesLeft :
  (x y z : Cyclotomic5) →
  _*5_ x (_+5_ y z) ≡ _+5_ (_*5_ x y) (_*5_ x z)
scalarMulDistributesLeft (cyc5 a b c d) (cyc5 e f g h) (cyc5 i j k l) =
  cyc5-ext solve-∀ solve-∀ solve-∀ solve-∀

-- The proof-critical part is distributivity, not the cyclic index
-- counts. Finite sum-swap/scale can now reuse the original generic
-- Grafakos and NS proof patterns at their actual cyclotomic types.
