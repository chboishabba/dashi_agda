module DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

data TriQuadratic : Set where
  qnil  : TriQuadratic
  qcons : ℚ → List ℚ → TriQuadratic → TriQuadratic

dot : List ℚ → List ℚ → ℚ
dot [] ys = 0ℚ
dot xs [] = 0ℚ
dot (a ∷ as) (x ∷ xs) = a * x + dot as xs

scaleList : ℚ → List ℚ → List ℚ
scaleList scalar [] = []
scaleList scalar (x ∷ xs) = scalar * x ∷ scaleList scalar xs

addList : List ℚ → List ℚ → List ℚ
addList [] ys = ys
addList xs [] = xs
addList (x ∷ xs) (y ∷ ys) = (x + y) ∷ addList xs ys

scaleTri : ℚ → TriQuadratic → TriQuadratic
scaleTri scalar qnil = qnil
scaleTri scalar (qcons diagonal row tail) =
  qcons (scalar * diagonal) (scaleList scalar row) (scaleTri scalar tail)

addTri : TriQuadratic → TriQuadratic → TriQuadratic
addTri qnil right = right
addTri left qnil = left
addTri (qcons dl rl tl) (qcons dr rr tr) =
  qcons (dl + dr) (addList rl rr) (addTri tl tr)

evalTri : TriQuadratic → List ℚ → ℚ
evalTri qnil xs = 0ℚ
evalTri (qcons diagonal row tail) [] = 0ℚ
evalTri (qcons diagonal row tail) (x ∷ xs) =
  diagonal * x * x + x * dot row xs + evalTri tail xs

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

scalarMulZeroRaw : ∀ s → 0ℚ ≡ s * 0ℚ
scalarMulZeroRaw = ℚRing.solve-∀

zeroPlusZeroRaw : 0ℚ ≡ 0ℚ + 0ℚ
zeroPlusZeroRaw = ℚRing.solve-∀

zeroPlusRaw : ∀ y → y ≡ 0ℚ + y
zeroPlusRaw = ℚRing.solve-∀

plusZeroRaw : ∀ y → y ≡ y + 0ℚ
plusZeroRaw = ℚRing.solve-∀

zeroMulZeroRaw : 0ℚ * 0ℚ ≡ 0ℚ
zeroMulZeroRaw = ℚRing.solve-∀

dotScaleStepRaw : ∀ s a x d →
  (s * a) * x + s * d ≡ s * (a * x + d)
dotScaleStepRaw = ℚRing.solve-∀

dotScale : ∀ scalar coefficients coordinates →
  dot (scaleList scalar coefficients) coordinates
  ≡ scalar * dot coefficients coordinates
dotScale scalar [] coordinates = scalarMulZeroRaw scalar
dotScale scalar (a ∷ as) [] = scalarMulZeroRaw scalar
dotScale scalar (a ∷ as) (x ∷ xs)
  rewrite dotScale scalar as xs = dotScaleStepRaw scalar a x (dot as xs)

dotAddStepRaw : ∀ a b x da db →
  (a + b) * x + (da + db) ≡ (a * x + da) + (b * x + db)
dotAddStepRaw = ℚRing.solve-∀

dotAdd : ∀ left right coordinates →
  dot (addList left right) coordinates
  ≡ dot left coordinates + dot right coordinates
dotAdd [] right coordinates = zeroPlusRaw (dot right coordinates)
dotAdd (a ∷ as) [] coordinates = plusZeroRaw (dot (a ∷ as) coordinates)
dotAdd (a ∷ as) (b ∷ bs) [] = zeroPlusZeroRaw
dotAdd (a ∷ as) (b ∷ bs) (x ∷ xs)
  rewrite dotAdd as bs xs = dotAddStepRaw a b x (dot as xs) (dot bs xs)

evalScaleStepRaw : ∀ s d x r t →
  (s * d) * x * x + x * (s * r) + s * t
  ≡ s * (d * x * x + x * r + t)
evalScaleStepRaw = ℚRing.solve-∀

evalScale : ∀ scalar quadratic coordinates →
  evalTri (scaleTri scalar quadratic) coordinates
  ≡ scalar * evalTri quadratic coordinates
evalScale scalar qnil coordinates = scalarMulZeroRaw scalar
evalScale scalar (qcons diagonal row tail) [] = scalarMulZeroRaw scalar
evalScale scalar (qcons diagonal row tail) (x ∷ xs)
  rewrite dotScale scalar row xs
        | evalScale scalar tail xs
  = evalScaleStepRaw scalar diagonal x (dot row xs) (evalTri tail xs)

evalAddStepRaw : ∀ dl dr x rl rr tl tr →
  (dl + dr) * x * x + x * (rl + rr) + (tl + tr)
  ≡ (dl * x * x + x * rl + tl) + (dr * x * x + x * rr + tr)
evalAddStepRaw = ℚRing.solve-∀

evalAdd : ∀ left right coordinates →
  evalTri (addTri left right) coordinates
  ≡ evalTri left coordinates + evalTri right coordinates
evalAdd qnil right coordinates = zeroPlusRaw (evalTri right coordinates)
evalAdd (qcons dl rl tl) qnil coordinates = plusZeroRaw (evalTri (qcons dl rl tl) coordinates)
evalAdd (qcons dl rl tl) (qcons dr rr tr) [] = zeroPlusZeroRaw
evalAdd (qcons dl rl tl) (qcons dr rr tr) (x ∷ xs)
  rewrite dotAdd rl rr xs
        | evalAdd tl tr xs
  = evalAddStepRaw dl dr x (dot rl xs) (dot rr xs) (evalTri tl xs) (evalTri tr xs)

squareLinear : List ℚ → TriQuadratic
squareLinear [] = qnil
squareLinear (a ∷ as) =
  qcons (a * a) (scaleList (twoℚ * a) as) (squareLinear as)

squareDotStepRaw : ∀ a x d →
  (a * x + d) * (a * x + d)
  ≡ (a * a) * x * x + x * ((twoℚ * a) * d) + (d * d)
squareDotStepRaw = ℚRing.solve-∀

squareDot : ∀ coefficients coordinates →
  dot coefficients coordinates * dot coefficients coordinates
  ≡ evalTri (squareLinear coefficients) coordinates
squareDot [] coordinates = zeroMulZeroRaw
squareDot (a ∷ as) [] = zeroMulZeroRaw
squareDot (a ∷ as) (x ∷ xs)
  rewrite dotScale (twoℚ * a) as xs
        | sym (squareDot as xs)
  = squareDotStepRaw a x (dot as xs)

sumSquareTri : List (List ℚ) → TriQuadratic
sumSquareTri [] = qnil
sumSquareTri (coefficients ∷ rest) =
  addTri (squareLinear coefficients) (sumSquareTri rest)

sumSquareValues : List (List ℚ) → List ℚ → ℚ
sumSquareValues [] coordinates = 0ℚ
sumSquareValues (coefficients ∷ rest) coordinates =
  dot coefficients coordinates * dot coefficients coordinates
  + sumSquareValues rest coordinates

sumSquareCompiler : ∀ families coordinates →
  evalTri (sumSquareTri families) coordinates
  ≡ sumSquareValues families coordinates
sumSquareCompiler [] coordinates = refl
sumSquareCompiler (coefficients ∷ rest) coordinates =
  trans
    (evalAdd (squareLinear coefficients) (sumSquareTri rest) coordinates)
    (cong₂ _+_
      (sym (squareDot coefficients coordinates))
      (sumSquareCompiler rest coordinates))

weightedSquareTri : ℚ → List ℚ → TriQuadratic
weightedSquareTri weight coefficients = scaleTri weight (squareLinear coefficients)

sumWeightedSquareTri : List (ℚ × List ℚ) → TriQuadratic
sumWeightedSquareTri [] = qnil
sumWeightedSquareTri ((weight , coefficients) ∷ rest) =
  addTri (weightedSquareTri weight coefficients) (sumWeightedSquareTri rest)

sumWeightedSquareValues : List (ℚ × List ℚ) → List ℚ → ℚ
sumWeightedSquareValues [] coordinates = 0ℚ
sumWeightedSquareValues ((weight , coefficients) ∷ rest) coordinates =
  weight * (dot coefficients coordinates * dot coefficients coordinates)
  + sumWeightedSquareValues rest coordinates

weightedSquareCompiler : ∀ weight coefficients coordinates →
  evalTri (weightedSquareTri weight coefficients) coordinates
  ≡ weight * (dot coefficients coordinates * dot coefficients coordinates)
weightedSquareCompiler weight coefficients coordinates =
  trans
    (evalScale weight (squareLinear coefficients) coordinates)
    (cong (λ value → weight * value) (sym (squareDot coefficients coordinates)))

sumWeightedSquareCompiler : ∀ families coordinates →
  evalTri (sumWeightedSquareTri families) coordinates
  ≡ sumWeightedSquareValues families coordinates
sumWeightedSquareCompiler [] coordinates = refl
sumWeightedSquareCompiler ((weight , coefficients) ∷ rest) coordinates =
  trans
    (evalAdd
      (weightedSquareTri weight coefficients)
      (sumWeightedSquareTri rest)
      coordinates)
    (cong₂ _+_
      (weightedSquareCompiler weight coefficients coordinates)
      (sumWeightedSquareCompiler rest coordinates))

qconsCong : ∀ {d d' row row' tail tail'} →
  d ≡ d' → row ≡ row' → tail ≡ tail' →
  qcons d row tail ≡ qcons d' row' tail'
qconsCong refl refl refl = refl
