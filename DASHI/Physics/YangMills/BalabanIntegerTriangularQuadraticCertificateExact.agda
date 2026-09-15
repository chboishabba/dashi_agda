module DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact where

------------------------------------------------------------------------
-- Native integer quadratic-certificate carrier.
--
-- This owner deliberately contains no Data.Rational import.  Closed certificate
-- arithmetic therefore stays in Data.Integer, whose Nat addition/multiplication
-- backend is primitive/bignum-backed, rather than entering rational normalize,
-- gcd, or Nat div-helper.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; _+_; _*_; -_)
open import Data.Product using (_×_; _,_)

zeroZ : ℤ
zeroZ = + 0

twoZ : ℤ
twoZ = + 2

data TriQuadraticZ : Set where
  qnilZ  : TriQuadraticZ
  qconsZ : ℤ → List ℤ → TriQuadraticZ → TriQuadraticZ

scaleListZ : ℤ → List ℤ → List ℤ
scaleListZ scalar [] = []
scaleListZ scalar (x ∷ xs) = scalar * x ∷ scaleListZ scalar xs

addListZ : List ℤ → List ℤ → List ℤ
addListZ [] ys = ys
addListZ xs [] = xs
addListZ (x ∷ xs) (y ∷ ys) = (x + y) ∷ addListZ xs ys

scaleTriZ : ℤ → TriQuadraticZ → TriQuadraticZ
scaleTriZ scalar qnilZ = qnilZ
scaleTriZ scalar (qconsZ diagonal row tail) =
  qconsZ (scalar * diagonal) (scaleListZ scalar row) (scaleTriZ scalar tail)

addTriZ : TriQuadraticZ → TriQuadraticZ → TriQuadraticZ
addTriZ qnilZ right = right
addTriZ left qnilZ = left
addTriZ (qconsZ dl rl tl) (qconsZ dr rr tr) =
  qconsZ (dl + dr) (addListZ rl rr) (addTriZ tl tr)

squareLinearZ : List ℤ → TriQuadraticZ
squareLinearZ [] = qnilZ
squareLinearZ (a ∷ as) =
  qconsZ (a * a) (scaleListZ (twoZ * a) as) (squareLinearZ as)

sumSquareTriZ : List (List ℤ) → TriQuadraticZ
sumSquareTriZ [] = qnilZ
sumSquareTriZ (coefficients ∷ rest) =
  addTriZ (squareLinearZ coefficients) (sumSquareTriZ rest)

weightedSquareTriZ : ℤ → List ℤ → TriQuadraticZ
weightedSquareTriZ weight coefficients =
  scaleTriZ weight (squareLinearZ coefficients)

sumWeightedSquareTriZ : List (ℤ × List ℤ) → TriQuadraticZ
sumWeightedSquareTriZ [] = qnilZ
sumWeightedSquareTriZ ((weight , coefficients) ∷ rest) =
  addTriZ
    (weightedSquareTriZ weight coefficients)
    (sumWeightedSquareTriZ rest)

diagOfZ : TriQuadraticZ → ℤ
diagOfZ qnilZ = zeroZ
diagOfZ (qconsZ diagonal row tail) = diagonal

rowOfZ : TriQuadraticZ → List ℤ
rowOfZ qnilZ = []
rowOfZ (qconsZ diagonal row tail) = row

tailOfZ : TriQuadraticZ → TriQuadraticZ
tailOfZ qnilZ = qnilZ
tailOfZ (qconsZ diagonal row tail) = tail

qconsCongZ : ∀ {d d' row row' tail tail'} →
  d ≡ d' → row ≡ row' → tail ≡ tail' →
  qconsZ d row tail ≡ qconsZ d' row' tail'
qconsCongZ refl refl refl = refl
