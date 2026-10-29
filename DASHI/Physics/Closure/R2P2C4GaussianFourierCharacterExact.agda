module DASHI.Physics.Closure.R2P2C4GaussianFourierCharacterExact where

------------------------------------------------------------------------
-- SOURCE-WRITTEN EXACT C4 CHARACTER / ORTHOGONALITY LAYER OVER Q(i).
--
-- Original finite Fourier / rational algebra owners:
--   R2P227729FourGridRetainedQuadraticParetoExact (actual Z/4 group),
--   C3CubeCyclotomicFourierExact (the *different* Q(omega) C3 DFT),
--   Patterson/Orszag classic finite spectral dealiasing.
--
-- Distinguish i^4=1 from omega^3=1. This module does NOT construct
-- the entire C4^3 sampled-field forward/inverse FFT or NS projection.
-- Kernel status PENDING; source-written terms are not kernel receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
import DASHI.Physics.Closure.R2P227729FourGridRetainedQuadraticParetoExact as Four

record Gaussian4 : Set where
  constructor gauss
  field realPart imaginaryPart : ℚ
open Gaussian4 public

zeroG oneG iG negOneG negIG : Gaussian4
zeroG = gauss 0ℚ 0ℚ
oneG = gauss 1ℚ 0ℚ
iG = gauss 0ℚ 1ℚ
negOneG = gauss (- 1ℚ) 0ℚ
negIG = gauss 0ℚ (- 1ℚ)

infixl 6 _+G_
infixl 7 _*G_

_+G_ : Gaussian4 → Gaussian4 → Gaussian4
gauss a b +G gauss c d = gauss (a + c) (b + d)

_*G_ : Gaussian4 → Gaussian4 → Gaussian4
gauss a b *G gauss c d =
  gauss (a * c - b * d) (a * d + b * c)

conjG : Gaussian4 → Gaussian4
conjG (gauss a b) = gauss a (- b)

gauss-ext : ∀ {a b c d} → a ≡ c → b ≡ d →
  gauss a b ≡ gauss c d
gauss-ext refl refl = refl

iSquared : iG *G iG ≡ negOneG
iSquared = gauss-ext solve-∀ solve-∀

iFourth : (iG *G iG) *G (iG *G iG) ≡ oneG
iFourth = gauss-ext solve-∀ solve-∀

gaussianConjMul :
  (a b : Gaussian4) → conjG (a *G b) ≡ conjG a *G conjG b
gaussianConjMul (gauss a b) (gauss c d) =
  gauss-ext solve-∀ solve-∀

root4 : Four.FourGridMode → Gaussian4
root4 Four.fourZero = oneG
root4 Four.fourPlusOne = iG
root4 Four.fourOuterTwo = negOneG
root4 Four.fourMinusOne = negIG

-- Correct cyclic ring multiplication k*x modulo four. It is NOT the
-- group addition operation supplied by the source owner.
scalarProduct4 : Four.FourGridMode → Four.FourGridMode → Four.FourGridMode
scalarProduct4 Four.fourZero Four.fourZero = Four.fourZero
scalarProduct4 Four.fourZero Four.fourPlusOne = Four.fourZero
scalarProduct4 Four.fourZero Four.fourOuterTwo = Four.fourZero
scalarProduct4 Four.fourZero Four.fourMinusOne = Four.fourZero
scalarProduct4 Four.fourPlusOne Four.fourZero = Four.fourZero
scalarProduct4 Four.fourPlusOne Four.fourPlusOne = Four.fourPlusOne
scalarProduct4 Four.fourPlusOne Four.fourOuterTwo = Four.fourOuterTwo
scalarProduct4 Four.fourPlusOne Four.fourMinusOne = Four.fourMinusOne
scalarProduct4 Four.fourOuterTwo Four.fourZero = Four.fourZero
scalarProduct4 Four.fourOuterTwo Four.fourPlusOne = Four.fourOuterTwo
scalarProduct4 Four.fourOuterTwo Four.fourOuterTwo = Four.fourZero
scalarProduct4 Four.fourOuterTwo Four.fourMinusOne = Four.fourOuterTwo
scalarProduct4 Four.fourMinusOne Four.fourZero = Four.fourZero
scalarProduct4 Four.fourMinusOne Four.fourPlusOne = Four.fourMinusOne
scalarProduct4 Four.fourMinusOne Four.fourOuterTwo = Four.fourOuterTwo
scalarProduct4 Four.fourMinusOne Four.fourMinusOne = Four.fourPlusOne

-- Reuses the ORIGINAL Z/4 group addition operation, without inventing
-- a second incompatible cyclic group table.
rootGroupLaw :
  (a b : Four.FourGridMode) →
  root4 (Four.fourGroupAdd a b) ≡ root4 a *G root4 b
rootGroupLaw Four.fourZero Four.fourZero = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourZero Four.fourPlusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourZero Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourZero Four.fourMinusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourPlusOne Four.fourZero = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourPlusOne Four.fourPlusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourPlusOne Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourPlusOne Four.fourMinusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourOuterTwo Four.fourZero = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourOuterTwo Four.fourPlusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourOuterTwo Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourOuterTwo Four.fourMinusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourMinusOne Four.fourZero = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourMinusOne Four.fourPlusOne = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourMinusOne Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
rootGroupLaw Four.fourMinusOne Four.fourMinusOne = gauss-ext solve-∀ solve-∀

character4 : Four.FourGridMode → Four.FourGridMode → Gaussian4
character4 k x = root4 (scalarProduct4 k x)

sum4 : (Four.FourGridMode → Gaussian4) → Gaussian4
sum4 f =
  f Four.fourZero +G f Four.fourPlusOne +G
  f Four.fourOuterTwo +G f Four.fourMinusOne

inner4 : Four.FourGridMode → Four.FourGridMode → Gaussian4
inner4 k l = sum4 λ x → character4 k x *G conjG (character4 l x)

fourG : Gaussian4
fourG = gauss (1ℚ + 1ℚ + 1ℚ + 1ℚ) 0ℚ

delta4 : Four.FourGridMode → Four.FourGridMode → Gaussian4
delta4 k l with Four.eqFour k l
... | true = fourG
... | false = zeroG

oneDimensionalCharacterOrthogonality :
  (k l : Four.FourGridMode) → inner4 k l ≡ delta4 k l
oneDimensionalCharacterOrthogonality Four.fourZero Four.fourZero = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourZero Four.fourPlusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourZero Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourZero Four.fourMinusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourPlusOne Four.fourZero = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourPlusOne Four.fourPlusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourPlusOne Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourPlusOne Four.fourMinusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourOuterTwo Four.fourZero = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourOuterTwo Four.fourPlusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourOuterTwo Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourOuterTwo Four.fourMinusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourMinusOne Four.fourZero = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourMinusOne Four.fourPlusOne = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourMinusOne Four.fourOuterTwo = gauss-ext solve-∀ solve-∀
oneDimensionalCharacterOrthogonality Four.fourMinusOne Four.fourMinusOne = gauss-ext solve-∀ solve-∀

-- Exact separable three-axis character norm. The source C3^3 theorem
-- is NOT reused as a C4^3 theorem, because these roots differ.
record Cube4 : Set where
  constructor cube4
  field x y z : Four.FourGridMode
open Cube4 public

cubeInner4 : Cube4 → Cube4 → Gaussian4
cubeInner4 (cube4 a b c) (cube4 d e f) =
  inner4 a d *G inner4 b e *G inner4 c f

cubeDelta4 : Cube4 → Cube4 → Gaussian4
cubeDelta4 (cube4 a b c) (cube4 d e f) =
  delta4 a d *G delta4 b e *G delta4 c f

cubeCharacterOrthogonality :
  (k l : Cube4) → cubeInner4 k l ≡ cubeDelta4 k l
cubeCharacterOrthogonality (cube4 a b c) (cube4 d e f)
  rewrite oneDimensionalCharacterOrthogonality a d
        | oneDimensionalCharacterOrthogonality b e
        | oneDimensionalCharacterOrthogonality c f = refl

cubeSelfNorm64 :
  cubeInner4
    (cube4 Four.fourPlusOne Four.fourPlusOne Four.fourPlusOne)
    (cube4 Four.fourPlusOne Four.fourPlusOne Four.fourPlusOne)
  ≡ gauss 64 0ℚ
cubeSelfNorm64 = gauss-ext solve-∀ solve-∀

-- Still-open: full sampled-field C4 tensor forward/inverse, normalized
-- 1/64 pointwise quadratic product, Nyquist fixed-mode reality and
-- actual NS/Leray lift.
