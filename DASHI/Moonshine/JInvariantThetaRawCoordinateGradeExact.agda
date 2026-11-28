module DASHI.Moonshine.JInvariantThetaRawCoordinateGradeExact where

-- Raw signed integer and odd-coordinate labels for the original scans.
-- The two signs are not duplicate labels; degree map may repeat values.
-- SOURCE-WRITTEN, kernel pending.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_; _*_ to _*N_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _-_; _*_; ∣_∣)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)
open import Data.List.Base using (List; []; _∷_; _++_; map; cartesianProductWith; filter)
open import Data.Product.Base using (_×_; _,_)
open import Data.Nat.Properties using (_≟_)
open import Data.Nat.Base using (_≤_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Moonshine.JInvariantThetaHadamardIntegralChartExact as H
import DASHI.Moonshine.JInvariantThetaGradedCauchyCountExact as G
import DASHI.Moonshine.JInvariantThetaBoundedScanReadoutExact as S
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W

pos : Nat → List ℤ
pos zero = []
pos (suc k) = (+ suc k) ∷ pos k

neg : Nat → List ℤ
neg zero = []
neg (suc k) = -[1+ k ] ∷ neg k

integerLabels : Nat → List ℤ
integerLabels k = (+ 0) ∷ (pos k ++ neg k)

-- Odd labels are parameters z of the actual odd coordinate 2z+1.
-- They use both signs even at magnitude index zero, unlike square labels.
posHalf negHalf : Nat → List ℤ
posHalf zero = (+ 0) ∷ []
posHalf (suc k) = (+ suc k) ∷ posHalf k
negHalf zero = -[1+ 0 ] ∷ []
negHalf (suc k) = -[1+ suc k ] ∷ negHalf k

oddLabels : Nat → List ℤ
oddLabels k = posHalf k ++ negHalf k

squareGrade : ℤ → Nat
squareGrade z = T.sqN ∣ z ∣

halfGrade : ℤ → Nat
halfGrade (+ n) = T.triN n
halfGrade -[1+ n ] = T.triN n

oddCoordinate : ℤ → ℤ
oddCoordinate z = (+ 2) * z + (+ 1)

squareGradeRead : ∀ z → z * z ≡ + squareGrade z
squareGradeRead (+ n) = refl
squareGradeRead -[1+ n ] = refl

halfGradeRead : ∀ z → oddCoordinate z * oddCoordinate z ≡ (+ 4) * (+ halfGrade z) + (+ 1)
halfGradeRead (+ n) = solve 1
  (λ x → (con (+ 2) :* x :+ con (+ 1)) :* (con (+ 2) :* x :+ con (+ 1))
    := con (+ 4) :* (x :* (x :+ con (+ 1))) :+ con (+ 1)) refl (+ n)
halfGradeRead -[1+ n ] =
  -- -[1+n] is -(n+1), so the same triangular grade is retained.
  solve 1 (λ x →
    (con (+ 2) :* (con (+ 0) :- (x :+ con (+ 1))) :+ con (+ 1)) :*
    (con (+ 2) :* (con (+ 0) :- (x :+ con (+ 1))) :+ con (+ 1))
    := con (+ 4) :* (x :* (x :+ con (+ 1))) :+ con (+ 1)) refl (+ n)

mapAppend : ∀ {A B : Set} (f : A → B) xs ys →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
mapAppend f [] ys = refl
mapAppend f (x ∷ xs) ys = cong (f x ∷_) (mapAppend f xs ys)

positiveRead : ∀ k → map squareGrade (pos k) ≡ S.positive T.sqN k
positiveRead zero = refl
positiveRead (suc k) = cong (T.sqN (suc k) ∷_) (positiveRead k)

negativeRead : ∀ k → map squareGrade (neg k) ≡ S.positive T.sqN k
negativeRead zero = refl
negativeRead (suc k) = cong (T.sqN (suc k) ∷_) (negativeRead k)

squareLabelsRead : ∀ k → map squareGrade (integerLabels k) ≡ S.squareScan k
squareLabelsRead k = cong (zero ∷_)
  (trans (mapAppend squareGrade (pos k) (neg k))
    (cong₂ _++_ (positiveRead k) (negativeRead k)))

posHalfRead : ∀ k → map halfGrade (posHalf k) ≡ S.scan T.triN k
posHalfRead zero = refl
posHalfRead (suc k) = cong (T.triN (suc k) ∷_) (posHalfRead k)

negHalfRead : ∀ k → map halfGrade (negHalf k) ≡ S.scan T.triN k
negHalfRead zero = refl
negHalfRead (suc k) = cong (T.triN (suc k) ∷_) (negHalfRead k)

halfLabelsRead : ∀ k → map halfGrade (oddLabels k) ≡
  S.scan T.triN k ++ S.scan T.triN k
halfLabelsRead k = trans (mapAppend halfGrade (posHalf k) (negHalf k))
  (cong₂ _++_ (posHalfRead k) (negHalfRead k))

-- Cartesian four-coordinate enumeration on retained labels. It is
-- intentionally balanced as ((a,b),(c,d)) to match the original rowZ.
Pairs : Set
Pairs = (ℤ × ℤ) × (ℤ × ℤ)

quadOf : Pairs → H.Quad
quadOf ((a , b) , (c , d)) = H.quad a b c d

fourLabels : List ℤ → List Pairs
fourLabels xs = cartesianProductWith _,_ (cartesianProductWith _,_ xs xs)
  (cartesianProductWith _,_ xs xs)

pairGrade : (ℤ → Nat) → ℤ × ℤ → Nat
pairGrade g (a , b) = g a +N g b

grade : (ℤ → Nat) → Pairs → Nat
grade g (ab , cd) = pairGrade g ab +N pairGrade g cd

fourLabelRead : ∀ g xs → map (grade g) (fourLabels xs) ≡ G.fourGrades (map g xs)
fourLabelRead g xs =
  trans (G.pairMap (pairGrade g) (pairGrade g)
    (cartesianProductWith _,_ xs xs) (cartesianProductWith _,_ xs xs))
    (cong₂ G.pairGrades (G.pairMap g g xs xs) (G.pairMap g g xs xs))

histFilter : ∀ {A : Set} (g : A → Nat) xs n →
  G.hist (map g xs) n ≡ + W.listLength (filter (λ x → g x ≟ n) xs)
histFilter g [] n = refl
histFilter g (x ∷ xs) n with g x ≟ n
... | yes eq rewrite eq | S.deltaSame n | histFilter g xs n = refl
... | no ne rewrite S.deltaDifferent (g x) n ne | histFilter g xs n = refl

integerList : Nat → Nat → List Pairs
integerList cutoff n = filter (λ x → grade squareGrade x ≟ n) (fourLabels (integerLabels cutoff))

oddList : Nat → Nat → List Pairs
oddList cutoff n = filter (λ x → grade halfGrade x ≟ n) (fourLabels (oddLabels cutoff))

integerCount : ∀ cutoff n → n ≤ cutoff →
  (+ W.listLength (integerList cutoff n)) ≡ T.B n
integerCount cutoff n h =
  trans (sym (histFilter (grade squareGrade) (fourLabels (integerLabels cutoff)) n))
    (trans (cong (λ xs → G.hist xs n) (fourLabelRead squareGrade (integerLabels cutoff)))
      (trans (cong (λ xs → G.hist (G.fourGrades xs) n) (squareLabelsRead cutoff))
        (S.BCount cutoff n h)))
