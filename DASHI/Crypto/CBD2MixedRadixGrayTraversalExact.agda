module DASHI.Crypto.CBD2MixedRadixGrayTraversalExact where

------------------------------------------------------------------------
-- MIXED-RADIX GRAY TRAVERSAL FOR A CBD2 COEFFICIENT PAIR
--
-- A CBD2 coefficient has five centered values {-2,-1,0,1,2}.  After shifting
-- to digits {0,1,2,3,4}, the two-coordinate candidate carrier has 25 states.
--
-- Ordinary row-major enumeration has four row-boundary jumps of Manhattan
-- length five, giving total transition cost 40.  A boustrophedon/Gray traversal
-- reverses every second row; every one of its 24 transitions changes exactly
-- one digit by one step, giving transition cost 24.
--
-- This changes traversal/update geometry, not the exponential candidate count.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_∸_; _≤_)

------------------------------------------------------------------------
-- Five-value coefficient digit.
------------------------------------------------------------------------

data D5 : Set where d0 d1 d2 d3 d4 : D5

digit : D5 → Nat
digit d0 = 0
digit d1 = 1
digit d2 = 2
digit d3 = 3
digit d4 = 4

natDistance : Nat → Nat → Nat
natDistance a b = (a ∸ b) + (b ∸ a)

digitDistance : D5 → D5 → Nat
digitDistance a b = natDistance (digit a) (digit b)

record CBD2Pair : Set where
  constructor cbd2Pair
  field x y : D5
open CBD2Pair public

pairDistance : CBD2Pair → CBD2Pair → Nat
pairDistance a b =
  digitDistance (x a) (x b) + digitDistance (y a) (y b)

pathCost : List CBD2Pair → Nat
pathCost [] = 0
pathCost (_ ∷ []) = 0
pathCost (a ∷ b ∷ rest) = pairDistance a b + pathCost (b ∷ rest)

pathLength : {A : Set} → List A → Nat
pathLength [] = 0
pathLength (_ ∷ xs) = suc (pathLength xs)

------------------------------------------------------------------------
-- Lexicographic / row-major order.
------------------------------------------------------------------------

lexPath : List CBD2Pair
lexPath =
  cbd2Pair d0 d0 ∷ cbd2Pair d0 d1 ∷ cbd2Pair d0 d2 ∷ cbd2Pair d0 d3 ∷ cbd2Pair d0 d4 ∷
  cbd2Pair d1 d0 ∷ cbd2Pair d1 d1 ∷ cbd2Pair d1 d2 ∷ cbd2Pair d1 d3 ∷ cbd2Pair d1 d4 ∷
  cbd2Pair d2 d0 ∷ cbd2Pair d2 d1 ∷ cbd2Pair d2 d2 ∷ cbd2Pair d2 d3 ∷ cbd2Pair d2 d4 ∷
  cbd2Pair d3 d0 ∷ cbd2Pair d3 d1 ∷ cbd2Pair d3 d2 ∷ cbd2Pair d3 d3 ∷ cbd2Pair d3 d4 ∷
  cbd2Pair d4 d0 ∷ cbd2Pair d4 d1 ∷ cbd2Pair d4 d2 ∷ cbd2Pair d4 d3 ∷ cbd2Pair d4 d4 ∷ []

lexPathHas25States : pathLength lexPath ≡ 25
lexPathHas25States = refl

lexPathCost : pathCost lexPath ≡ 40
lexPathCost = refl

------------------------------------------------------------------------
-- Boustrophedon / mixed-radix Gray order.
------------------------------------------------------------------------

grayPath : List CBD2Pair
grayPath =
  cbd2Pair d0 d0 ∷ cbd2Pair d0 d1 ∷ cbd2Pair d0 d2 ∷ cbd2Pair d0 d3 ∷ cbd2Pair d0 d4 ∷
  cbd2Pair d1 d4 ∷ cbd2Pair d1 d3 ∷ cbd2Pair d1 d2 ∷ cbd2Pair d1 d1 ∷ cbd2Pair d1 d0 ∷
  cbd2Pair d2 d0 ∷ cbd2Pair d2 d1 ∷ cbd2Pair d2 d2 ∷ cbd2Pair d2 d3 ∷ cbd2Pair d2 d4 ∷
  cbd2Pair d3 d4 ∷ cbd2Pair d3 d3 ∷ cbd2Pair d3 d2 ∷ cbd2Pair d3 d1 ∷ cbd2Pair d3 d0 ∷
  cbd2Pair d4 d0 ∷ cbd2Pair d4 d1 ∷ cbd2Pair d4 d2 ∷ cbd2Pair d4 d3 ∷ cbd2Pair d4 d4 ∷ []

grayPathHas25States : pathLength grayPath ≡ 25
grayPathHas25States = refl

grayPathCost : pathCost grayPath ≡ 24
grayPathCost = refl

lexExcessTransitionCost : pathCost lexPath ≡ pathCost grayPath + 16
lexExcessTransitionCost = refl

------------------------------------------------------------------------
-- Generic positivity carrier for later arbitrary mixed-radix paths.
------------------------------------------------------------------------

data PositiveCostList : List Nat → Set where
  empty : PositiveCostList []
  cons : ∀ {c cs} → suc zero ≤ c → PositiveCostList cs → PositiveCostList (c ∷ cs)

sum : List Nat → Nat
sum [] = 0
sum (c ∷ cs) = c + sum cs

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

grayAttainsTwentyFourEdgeFloor : pathCost grayPath ≡ 24
grayAttainsTwentyFourEdgeFloor = refl

record MixedRadixTraversalComparison : Set where
  constructor mixedRadixTraversalComparison
  field
    candidateCount : Nat
    lexCost grayCost : Nat
    sameCandidateCount : candidateCount ≡ 25
    lexIs40 : lexCost ≡ 40
    grayIs24 : grayCost ≡ 24

open MixedRadixTraversalComparison public

cbd2TraversalComparison : MixedRadixTraversalComparison
cbd2TraversalComparison =
  mixedRadixTraversalComparison 25 40 24 refl refl refl
