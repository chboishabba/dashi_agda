module DASHI.Crypto.GrayPathTransitionOptimalExact where

------------------------------------------------------------------------
-- PATH TRANSITION GEOMETRY AND GRAY OPTIMALITY
--
-- Every distinct-code transition has positive Hamming cost, so any finite path
-- with m edges costs at least m.  A unit-edge realization attains that lower
-- bound.  The P4 Gray embedding is the concrete two-bit instance; ordinary
-- binary incurs one extra transition unit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-mono-≤)
open import Relation.Binary.PropositionalEquality using (cong; subst)

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
-- General unit-edge path realization.
------------------------------------------------------------------------

unitCosts : Nat → List Nat
unitCosts zero = []
unitCosts (suc n) = suc zero ∷ unitCosts n

unitCostsLength : ∀ n → length (unitCosts n) ≡ n
unitCostsLength zero = refl
unitCostsLength (suc n) = cong suc (unitCostsLength n)

unitCostsSum : ∀ n → sum (unitCosts n) ≡ n
unitCostsSum zero = refl
unitCostsSum (suc n) = cong suc (unitCostsSum n)

unitCostsPositive : ∀ n → PositiveCostList (unitCosts n)
unitCostsPositive zero = empty
unitCostsPositive (suc n) = cons (s≤s z≤n) (unitCostsPositive n)

positivePathCostAtLeastEdgeCount :
  ∀ {costs n} →
  PositiveCostList costs →
  length costs ≡ n →
  n ≤ sum costs
positivePathCostAtLeastEdgeCount {costs} {n} positive edgeCount =
  subst (λ m → m ≤ sum costs) edgeCount
    (sumAtLeastLength positive)

unitPathAttainsLowerBound : ∀ n → sum (unitCosts n) ≡ length (unitCosts n)
unitPathAttainsLowerBound zero = refl
unitPathAttainsLowerBound (suc n) = cong suc (unitPathAttainsLowerBound n)

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
