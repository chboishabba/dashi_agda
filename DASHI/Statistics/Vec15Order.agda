module DASHI.Statistics.Vec15Order where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _/_; _≤_)
open import Data.Nat.Properties as NatP using (_≤?_; ≤-refl)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- Order, selection, and threshold-mask helpers for the 15-lane Nat carrier.
--
-- The module stays finite and constructive:
--   - insertion sort on a concrete 15-element list view
--   - indexed selection from the sorted view
--   - threshold masks and rank counts
--   - small clamp / absolute-difference helpers for robust summaries

PrimeCarrier15 : Set
PrimeCarrier15 = Vec15 Nat

zeroCarrier15 : PrimeCarrier15
zeroCarrier15 = mkVec15 zero zero zero zero zero zero zero zero zero zero zero zero zero zero zero

one two three four five six seven eight nine ten eleven twelve thirteen fourteen : Nat
one = suc zero
two = suc one
three = suc two
four = suc three
five = suc four
six = suc five
seven = suc six
eight = suc seven
nine = suc eight
ten = suc nine
eleven = suc ten
twelve = suc eleven
thirteen = suc twelve
fourteen = suc thirteen

demoSortedCarrier15 : PrimeCarrier15
demoSortedCarrier15 =
  mkVec15 zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen

------------------------------------------------------------------------
-- Concrete list view.

toList15 : PrimeCarrier15 → List Nat
toList15 (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2 ∷ a3 ∷ a5 ∷ a7 ∷ a11 ∷ a13 ∷ a17 ∷ a19 ∷ a23 ∷ a29 ∷ a31 ∷ a41 ∷ a47 ∷ a59 ∷ a71 ∷ []

------------------------------------------------------------------------
-- Insertion sort, ascending.

insertAsc : Nat → List Nat → List Nat
insertAsc x [] = x ∷ []
insertAsc x (y ∷ ys) with x NatP.≤? y
... | yes _ = x ∷ y ∷ ys
... | no _  = y ∷ insertAsc x ys

sortAsc : List Nat → List Nat
sortAsc [] = []
sortAsc (x ∷ xs) = insertAsc x (sortAsc xs)

sortAsc-demoSortedCarrier15 : sortAsc (toList15 demoSortedCarrier15) ≡ toList15 demoSortedCarrier15
sortAsc-demoSortedCarrier15 = refl

------------------------------------------------------------------------
-- Indexed selection on the sorted list view.

nthOrZero : Nat → List Nat → Nat
nthOrZero zero    (x ∷ xs) = x
nthOrZero zero    []       = zero
nthOrZero (suc n) []       = zero
nthOrZero (suc n) (x ∷ xs) = nthOrZero n xs

selectAt15 : Nat → PrimeCarrier15 → Nat
selectAt15 n v = nthOrZero n (sortAsc (toList15 v))

selectAt15-demoSortedCarrier15-7 : selectAt15 7 demoSortedCarrier15 ≡ seven
selectAt15-demoSortedCarrier15-7 = refl

selectAt15-demoSortedCarrier15-14 : selectAt15 14 demoSortedCarrier15 ≡ fourteen
selectAt15-demoSortedCarrier15-14 = refl

-- Fixed 15-lane hinge positions:
--   lower quartile = 4th element
--   median         = 8th element
--   upper quartile  = 12th element

lowerQuartile15 : PrimeCarrier15 → Nat
lowerQuartile15 = selectAt15 3

median15 : PrimeCarrier15 → Nat
median15 = selectAt15 7

upperQuartile15 : PrimeCarrier15 → Nat
upperQuartile15 = selectAt15 11

------------------------------------------------------------------------
-- Threshold masks and rank.

natLeqBool : Nat → Nat → Bool
natLeqBool x y with x NatP.≤? y
... | yes _ = true
... | no _  = false

selectMask15 : Nat → PrimeCarrier15 → Vec15 Bool
selectMask15 threshold (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  mkVec15
    (natLeqBool a2 threshold)
    (natLeqBool a3 threshold)
    (natLeqBool a5 threshold)
    (natLeqBool a7 threshold)
    (natLeqBool a11 threshold)
    (natLeqBool a13 threshold)
    (natLeqBool a17 threshold)
    (natLeqBool a19 threshold)
    (natLeqBool a23 threshold)
    (natLeqBool a29 threshold)
    (natLeqBool a31 threshold)
    (natLeqBool a41 threshold)
    (natLeqBool a47 threshold)
    (natLeqBool a59 threshold)
    (natLeqBool a71 threshold)

selectMask15-demoSortedCarrier15-7 :
  selectMask15 7 demoSortedCarrier15 ≡
  mkVec15 true true true true true true true true false false false false false false false
selectMask15-demoSortedCarrier15-7 = refl

countBool : Bool → Nat
countBool false = zero
countBool true  = suc zero

countMask15 : Vec15 Bool → Nat
countMask15 (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  countBool b2 + countBool b3 + countBool b5 + countBool b7 + countBool b11 +
  countBool b13 + countBool b17 + countBool b19 + countBool b23 + countBool b29 +
  countBool b31 + countBool b41 + countBool b47 + countBool b59 + countBool b71

rank15 : Nat → PrimeCarrier15 → Nat
rank15 threshold v = countMask15 (selectMask15 threshold v)

rank15-demoSortedCarrier15-7 : rank15 7 demoSortedCarrier15 ≡ eight
rank15-demoSortedCarrier15-7 = refl

------------------------------------------------------------------------
-- Small constructive helpers used by the robust lane.

absDiffNat : Nat → Nat → Nat
absDiffNat x y with x NatP.≤? y
... | yes _ = y ∸ x
... | no _  = x ∸ y

map15 : (Nat → Nat) → PrimeCarrier15 → PrimeCarrier15
map15 f (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  mkVec15 (f a2) (f a3) (f a5) (f a7) (f a11) (f a13) (f a17) (f a19) (f a23)
          (f a29) (f a31) (f a41) (f a47) (f a59) (f a71)

clampNat : Nat → Nat → Nat → Nat
clampNat lo hi n with lo NatP.≤? n | n NatP.≤? hi
... | yes _ | yes _ = n
... | yes _ | no _  = hi
... | no _  | _     = lo

clampNat≤hi : ∀ lo hi n → lo ≤ hi → clampNat lo hi n ≤ hi
clampNat≤hi lo hi n lo≤hi with lo NatP.≤? n | n NatP.≤? hi
... | yes _ | yes n≤hi = n≤hi
... | yes _ | no _     = ≤-refl
... | no _  | _        = lo≤hi

clampNat≥lo : ∀ lo hi n → lo ≤ hi → lo ≤ clampNat lo hi n
clampNat≥lo lo hi n lo≤hi with lo NatP.≤? n | n NatP.≤? hi
... | yes lo≤n | yes _ = lo≤n
... | yes lo≤n | no _  = lo≤hi
... | no _     | _     = ≤-refl
