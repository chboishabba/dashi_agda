module DASHI.Crypto.GrayPathTransitionOptimalExact where

------------------------------------------------------------------------
-- PATH TRANSITION GEOMETRY AND GRAY OPTIMALITY
--
-- For a finite path, any injective code must assign distinct codewords to the
-- endpoints of each edge, hence every edge has positive code distance.  The
-- abstract lower-bound theorem below records that positive edge costs sum to at
-- least the number of path edges.  A concrete 2-bit Gray embedding of P4 attains
-- the bound exactly, whereas ordinary binary incurs one extra transition unit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-mono-≤)

sum : List Nat → Nat
sum [] = 0
sum (x ∷ xs) = x + sum xs

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

------------------------------------------------------------------------
-- Positivity evidence travels with each path edge.
------------------------------------------------------------------------

data PositiveCostList : List Nat → Set where
  empty : PositiveCostList []
  cons : ∀ {cost rest} → suc zero ≤ cost → PositiveCostList rest →
    PositiveCostList (cost ∷ rest)

sumAtLeastLength : ∀ {costs} → PositiveCostList costs → length costs ≤ sum costs
sumAtLeastLength empty = z≤n
sumAtLeastLength (cons one≤cost restPositive) =
  +-mono-≤ one≤cost (sumAtLeastLength restPositive)

------------------------------------------------------------------------
-- Two-bit Hamming metric.
------------------------------------------------------------------------

record Bit2 : Set where
  constructor bit2
  field first second : Bool
open Bit2 public

bitDiff : Bool → Bool → Nat
bitDiff false false = 0
bitDiff false true = 1
bitDiff true false = 1
bitDiff true true = 0

hamming2 : Bit2 → Bit2 → Nat
hamming2 a b = bitDiff (first a) (first b) + bitDiff (second a) (second b)

-- P4 ordinary binary: 00,01,10,11.
b0 b1 b2 b3 : Bit2
b0 = bit2 false false
b1 = bit2 false true
b2 = bit2 true false
b3 = bit2 true true

binaryPathCost : Nat
binaryPathCost = hamming2 b0 b1 + hamming2 b1 b2 + hamming2 b2 b3

binaryPathCostIs4 : binaryPathCost ≡ 4
binaryPathCostIs4 = refl

-- P4 Gray: 00,01,11,10.
g0 g1 g2 g3 : Bit2
g0 = bit2 false false
g1 = bit2 false true
g2 = bit2 true true
g3 = bit2 true false

grayEdgeCosts : List Nat
grayEdgeCosts = hamming2 g0 g1 ∷ hamming2 g1 g2 ∷ hamming2 g2 g3 ∷ []

grayEdgesPositive : PositiveCostList grayEdgeCosts
grayEdgesPositive = cons (s≤s z≤n) (cons (s≤s z≤n) (cons (s≤s z≤n) empty))

grayPathCost : Nat
grayPathCost = sum grayEdgeCosts

grayPathCostIs3 : grayPathCost ≡ 3
grayPathCostIs3 = refl

path4LowerBound : length grayEdgeCosts ≤ grayPathCost
path4LowerBound = sumAtLeastLength grayEdgesPositive

grayAttainsPath4LowerBound : grayPathCost ≡ length grayEdgeCosts
grayAttainsPath4LowerBound = refl

binaryStrictlyWorseThanGray : binaryPathCost ≡ suc grayPathCost
binaryStrictlyWorseThanGray = refl
