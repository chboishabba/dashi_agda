module DASHI.Mathematics.Arithmetic.EllipticCurveF5PointEnumerationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- Enumerate the affine F_5-points of y^2=x^3-x literally.  The five residue
-- classes, square table, x^3-x table, Boolean equality and all-y scan are finite
-- inductive data.  The fibre counts 1,1,2,2,1 and total affine count 7 reduce
-- by refl; adding the projective point at infinity gives 8.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (_×_; _,_)

data F5 : Set where
  f0 f1 f2 f3 f4 : F5

allF5 : List F5
allF5 = f0 ∷ f1 ∷ f2 ∷ f3 ∷ f4 ∷ []

f5Equals : F5 → F5 → Bool
f5Equals f0 f0 = true
f5Equals f0 _ = false
f5Equals f1 f1 = true
f5Equals f1 _ = false
f5Equals f2 f2 = true
f5Equals f2 _ = false
f5Equals f3 f3 = true
f5Equals f3 _ = false
f5Equals f4 f4 = true
f5Equals f4 _ = false

squareF5 : F5 → F5
squareF5 f0 = f0
squareF5 f1 = f1
squareF5 f2 = f4
squareF5 f3 = f4
squareF5 f4 = f1

cubeMinusSelfF5 : F5 → F5
cubeMinusSelfF5 f0 = f0
cubeMinusSelfF5 f1 = f0
cubeMinusSelfF5 f2 = f1
cubeMinusSelfF5 f3 = f4
cubeMinusSelfF5 f4 = f0

isAffineCurvePoint : F5 → F5 → Bool
isAffineCurvePoint x y =
  f5Equals (squareF5 y) (cubeMinusSelfF5 x)

boolToNat : Bool → Nat
boolToNat false = zero
boolToNat true = suc zero

countSolutionsForX : F5 → List F5 → Nat
countSolutionsForX x [] = zero
countSolutionsForX x (y ∷ ys) =
  boolToNat (isAffineCurvePoint x y) + countSolutionsForX x ys

fibreCount : F5 → Nat
fibreCount x = countSolutionsForX x allF5

fibreCount0 : fibreCount f0 ≡ 1
fibreCount0 = refl

fibreCount1 : fibreCount f1 ≡ 1
fibreCount1 = refl

fibreCount2 : fibreCount f2 ≡ 2
fibreCount2 = refl

fibreCount3 : fibreCount f3 ≡ 2
fibreCount3 = refl

fibreCount4 : fibreCount f4 ≡ 1
fibreCount4 = refl

fibreCountVector :
  fibreCount f0 ≡ 1
  × fibreCount f1 ≡ 1
  × fibreCount f2 ≡ 2
  × fibreCount f3 ≡ 2
  × fibreCount f4 ≡ 1
fibreCountVector = refl , refl , refl , refl , refl

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (value ∷ values) = value + sumNat values

affineFibreCounts : List Nat
affineFibreCounts =
  fibreCount f0 ∷ fibreCount f1 ∷ fibreCount f2 ∷
  fibreCount f3 ∷ fibreCount f4 ∷ []

affinePointCount : Nat
affinePointCount = sumNat affineFibreCounts

affinePointCountIsSeven : affinePointCount ≡ 7
affinePointCountIsSeven = refl

projectivePointCount : Nat
projectivePointCount = suc affinePointCount

projectivePointCountIsEight : projectivePointCount ≡ 8
projectivePointCountIsEight = refl

samplePoints :
  isAffineCurvePoint f2 f1 ≡ true
  × isAffineCurvePoint f2 f4 ≡ true
  × isAffineCurvePoint f3 f2 ≡ true
  × isAffineCurvePoint f3 f3 ≡ true
samplePoints = refl , refl , refl , refl

sampleNonPoint : isAffineCurvePoint f2 f2 ≡ false
sampleNonPoint = refl
