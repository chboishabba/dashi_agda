module DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact where

------------------------------------------------------------------------
-- FINITE BIPARTITE COVARIANCE CLOSED FORM
--
-- For disjoint or non-disjoint finite lists L,R (no hypothesis needed), define
--
--   B(L,R) = sum_{a in L} sum_{b in R}
--              (r_a-r_b)(w_a-w_b).
--
-- Exact finite algebra gives
--
--   B(L,R)
--     = |R| sum_L r_a w_a
--       + |L| sum_R r_b w_b
--       - (sum_L r_a)(sum_R w_b)
--       - (sum_R r_b)(sum_L w_a).
--
-- This is the cross-class analogue of pairDifferenceClosedForm.  It exposes
-- only four class aggregates and takes no absolute value or norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

bipartiteRow :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  A → List A → ℚ
bipartiteRow rate work left [] = 0ℚ
bipartiteRow rate work left (right ∷ rest) =
  (rate left - rate right) * (work left - work right)
  + bipartiteRow rate work left rest

bipartitePairSum :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  List A → List A → ℚ
bipartitePairSum rate work [] right = 0ℚ
bipartitePairSum rate work (left ∷ rest) right =
  bipartiteRow rate work left right
  + bipartitePairSum rate work rest right

bipartiteRowClosedForm :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left : A) →
  (right : List A) →
  bipartiteRow rate work left right
  ≡
    Pair.natAsRational (length right) * rate left * work left
    - rate left * Pair.workSum work right
    - Pair.rateSum rate right * work left
    + Pair.weightedWorkSum rate work right
bipartiteRowClosedForm rate work left [] = solve []
bipartiteRowClosedForm rate work left (right ∷ rest)
  rewrite bipartiteRowClosedForm rate work left rest =
  solve
    ( Pair.natAsRational (length rest)
    ∷ rate left ∷ work left
    ∷ rate right ∷ work right
    ∷ Pair.rateSum rate rest
    ∷ Pair.workSum work rest
    ∷ Pair.weightedWorkSum rate work rest
    ∷ [])

bipartiteClosedForm :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left right : List A) →
  bipartitePairSum rate work left right
  ≡
      Pair.natAsRational (length right)
        * Pair.weightedWorkSum rate work left
    + Pair.natAsRational (length left)
        * Pair.weightedWorkSum rate work right
    - Pair.rateSum rate left * Pair.workSum work right
    - Pair.rateSum rate right * Pair.workSum work left
bipartiteClosedForm rate work [] right = solve []
bipartiteClosedForm rate work (left ∷ rest) right
  rewrite bipartiteRowClosedForm rate work left right
        | bipartiteClosedForm rate work rest right =
  solve
    ( Pair.natAsRational (length right)
    ∷ Pair.natAsRational (length rest)
    ∷ rate left ∷ work left
    ∷ Pair.rateSum rate rest
    ∷ Pair.workSum work rest
    ∷ Pair.weightedWorkSum rate work rest
    ∷ Pair.rateSum rate right
    ∷ Pair.workSum work right
    ∷ Pair.weightedWorkSum rate work right
    ∷ [])

pairTermSymmetric :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left right : A) →
  (rate left - rate right) * (work left - work right)
  ≡
  (rate right - rate left) * (work right - work left)
pairTermSymmetric rate work left right =
  solve
    ( rate left ∷ rate right ∷ work left ∷ work right ∷ [])

bipartiteConsRight :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left : List A) →
  (head : A) →
  (right : List A) →
  bipartitePairSum rate work left (head ∷ right)
  ≡
  bipartiteRow rate work head left
    + bipartitePairSum rate work left right
bipartiteConsRight rate work [] head right = refl
bipartiteConsRight rate work (left ∷ rest) head right =
  trans
    (cong₂ _+_
      (cong₂ _+_
        (pairTermSymmetric rate work left head)
        (bipartiteRowTail left rest))
      (bipartiteConsRight rate work rest head right))
    (solve
      ( (rate head - rate left) * (work head - work left)
      ∷ bipartiteRow rate work head rest
      ∷ bipartiteRow rate work left right
      ∷ bipartitePairSum rate work rest right
      ∷ []))
  where
  bipartiteRowTail :
    (left : A) →
    (rest : List A) →
    bipartiteRow rate work left (head ∷ right)
    ≡
    (rate left - rate head) * (work left - work head)
      + bipartiteRow rate work left right
  bipartiteRowTail left rest = refl

bipartiteSymmetric :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left right : List A) →
  bipartitePairSum rate work left right
  ≡ bipartitePairSum rate work right left
bipartiteSymmetric rate work [] [] = refl
bipartiteSymmetric rate work [] (right ∷ rest) =
  emptyRight right rest
  where
  emptyRight :
    (head : A) → (tail : List A) →
    bipartitePairSum rate work (head ∷ tail) []
    ≡ 0ℚ
  emptyRight head tail =
    cong₂ _+_ refl (emptyTail tail)
    where
    emptyTail : (xs : List A) →
      bipartitePairSum rate work xs [] ≡ 0ℚ
    emptyTail [] = refl
    emptyTail (x ∷ xs) =
      cong₂ _+_ refl (emptyTail xs)
bipartiteSymmetric rate work (left ∷ rest) right =
  trans
    (bipartiteClosedForm rate work (left ∷ rest) right)
    (trans
      (solve
        ( Pair.natAsRational (length right)
        ∷ Pair.natAsRational (length rest)
        ∷ rate left ∷ work left
        ∷ Pair.rateSum rate rest
        ∷ Pair.workSum work rest
        ∷ Pair.weightedWorkSum rate work rest
        ∷ Pair.rateSum rate right
        ∷ Pair.workSum work right
        ∷ Pair.weightedWorkSum rate work right
        ∷ []))
      (sym (bipartiteClosedForm rate work right (left ∷ rest))))

finiteBipartiteCovarianceClosedFormClosed : Bool
finiteBipartiteCovarianceClosedFormClosed = true

finiteBipartiteCovarianceIntroducesAbsoluteValue : Bool
finiteBipartiteCovarianceIntroducesAbsoluteValue = false

finiteBipartiteCovarianceIntroducesCardinalityEstimate : Bool
finiteBipartiteCovarianceIntroducesCardinalityEstimate = false

clayPromotion : Bool
clayPromotion = false

finiteBipartiteCovarianceClosedFormClosedIsTrue :
  finiteBipartiteCovarianceClosedFormClosed ≡ true
finiteBipartiteCovarianceClosedFormClosedIsTrue = refl
