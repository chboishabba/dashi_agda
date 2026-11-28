{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySU2FejerProductFiniteExact where

-- YM.REAL / root-free S3 cubature FINITE producer (not the analytic producer).
-- Chebyshev-II m x Fejer-I 2m x circle 2m = 4m^3 nodes.
-- Fejer-I weights normalized for dt/2 use 1/M, not 2/M.
-- Theorem below builds actual finite product nodes and transports strict
-- positivity from the three factor lists. All-m Fourier exactness,
-- Bishop sine/cosine, and physical original Wilson attachment remain OPEN.
-- Attribution: Fejer; Stroud; Pizzetti/Folland; Bishop/Murray/Csimma;
-- Wilson/Balaban; original DASHI quaternion and finite-bond owners.

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

record Triple (A B C : Set) : Set where
  constructor triple
  field
    fst : A
    snd : B
    thd : C
open Triple public

record Weighted (Scalar Point : Set) : Set where
  constructor weighted
  field
    point : Point
    weight : Scalar
open Weighted public

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = append (f x) (concatMap f xs)

data All {A : Set} (P : A → Set) : List A → Set where
  allNil : All P []
  allCons : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

allMap : ∀ {A B : Set} {P : A → Set} {Q : B → Set}
  (f : A → B) → (∀ x → P x → Q (f x)) →
  ∀ {xs} → All P xs → All Q (map f xs)
allMap f step allNil = allNil
allMap f step {xs = x ∷ xs} (allCons px rest) =
  allCons (step x px) (allMap f step rest)

allAppend : ∀ {A : Set} {P : A → Set}
  {xs ys : List A} → All P xs → All P ys →
  All P (append xs ys)
allAppend allNil py = py
allAppend (allCons px rest) py =
  allCons px (allAppend rest py)

allConcatMap : ∀ {A B : Set} {P : A → Set} {Q : B → Set}
  (f : A → List B) →
  (∀ x → P x → All Q (f x)) →
  ∀ {xs} → All P xs → All Q (concatMap f xs)
allConcatMap f step allNil = allNil
allConcatMap f step {xs = x ∷ xs} (allCons px rest) =
  allAppend (step x px) (allConcatMap f step rest)

module _ {Scalar A B C : Set}
    (_times_ : Scalar → Scalar → Scalar)
    (StrictlyPositive : Scalar → Set)
    (positiveTimes : ∀ {x y} →
      StrictlyPositive x → StrictlyPositive y →
      StrictlyPositive (x times y))
  where

  combine : Weighted Scalar A → Weighted Scalar B →
    Weighted Scalar C → Weighted Scalar (Triple A B C)
  combine a b c =
    weighted
      (triple (point a) (point b) (point c))
      ((weight a times weight b) times weight c)

  combinePositive : ∀ a b c →
    StrictlyPositive (weight a) →
    StrictlyPositive (weight b) →
    StrictlyPositive (weight c) →
    StrictlyPositive (weight (combine a b c))
  combinePositive a b c pa pb pc =
    positiveTimes (positiveTimes pa pb) pc

  productNodes : List (Weighted Scalar A) →
    List (Weighted Scalar B) → List (Weighted Scalar C) →
    List (Weighted Scalar (Triple A B C))
  productNodes as bs cs =
    concatMap (λ a →
      concatMap (λ b → map (combine a b) cs) bs) as

  productNodesPositive : ∀ {as bs cs} →
    All (λ a → StrictlyPositive (weight a)) as →
    All (λ b → StrictlyPositive (weight b)) bs →
    All (λ c → StrictlyPositive (weight c)) cs →
    All (λ node → StrictlyPositive (weight node))
      (productNodes as bs cs)
  productNodesPositive {as} {bs} {cs} pas pbs pcs =
    allConcatMap
      (λ a → concatMap (λ b → map (combine a b) cs) bs)
      (λ a pa →
        allConcatMap
          (λ b → map (combine a b) cs)
          (λ b pb →
            allMap (combine a b)
              (λ c pc → combinePositive a b c pa pb pc) pcs)
          pbs)
      pas

rootFreeNodeBudget : Nat → Nat
rootFreeNodeBudget m = (2 * m) * ((2 * m) * m)
