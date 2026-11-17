module DASHI.Foundations.HypergeometricBSplitIntegerMergeExact where

------------------------------------------------------------------------
-- GENERIC INTEGER HYPERGEOMETRIC P/Q/B/T MERGE ALGEBRA
--
-- Classical binary splitting for rational hypergeometric terms;
-- Machin/Euler/Apery as sources for individual series, Bishop/Bridges
-- and Murray/Csimma for the downstream constructive-real completion.
--
-- This is finite INTEGER arithmetic, with no real-number postulate,
-- no external numeric oracle and no quotient by zero.
-- It proves the nontrivial associativity numerator identity required
-- by tree regrouping. It does not assert the missing finite-sum
-- semantics or identify any infinite Cauchy limit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

record SplitNode : Set where
  constructor node
  field
    P Q B T : ℤ
open SplitNode public

empty : SplitNode
empty = node 1ℤ 1ℤ 1ℤ 0ℤ

-- A leaf represents (a/b)*(p/q), so numerator a*p and
-- denominator b*q; P/Q carries the term-ratio product.
leaf : (a b p q : ℤ) → SplitNode
leaf a b p q = node p q b (a * p)

merge : SplitNode → SplitNode → SplitNode
merge L R =
  node
    (P L * P R)
    (Q L * Q R)
    (B L * B R)
    (T L * Q R * B R + P L * B L * T R)

-- The four-tuple numerator is associative even though the tree
-- grouping changes intermediate integer sizes.
mergeNumeratorAssociative :
  (pl bl tl pr br tr pc bc tc : ℤ) →
  ((tl * pr * br + pl * bl * tr) * pc * bc
    + (pl * pr) * (bl * br) * tc)
  ≡
  (tl * (pr * pc) * (br * bc)
    + pl * bl * (tr * pc * bc + pr * br * tc))
mergeNumeratorAssociative pl bl tl pr br tr pc bc tc =
  solve 9
    (λ pl bl tl pr br tr pc bc tc →
      (((tl :* pr :* br :+ pl :* bl :* tr)
         :* pc :* bc)
         :+ (pl :* pr) :* (bl :* br) :* tc)
      :=
      ((tl :* (pr :* pc) :* (br :* bc))
        :+ pl :* bl
          :* (tr :* pc :* bc :+ pr :* br :* tc)))
    refl pl bl tl pr br tr pc bc tc

mulAssociative :
  (a b c : ℤ) → (a * b) * c ≡ a * (b * c)
mulAssociative a b c =
  solve 3 (λ a b c → (a :* b) :* c := a :* (b :* c))
    refl a b c

nodeExt :
  ∀ {p q b t p' q' b' t'} →
  p ≡ p' → q ≡ q' → b ≡ b' → t ≡ t' →
  node p q b t ≡ node p' q' b' t'
nodeExt refl refl refl refl = refl

mergeAssociative :
  (L R C : SplitNode) →
  merge (merge L R) C ≡ merge L (merge R C)
mergeAssociative (node pl ql bl tl) (node pr qr br tr)
                 (node pc qc bc tc) =
  nodeExt
    (mulAssociative pl pr pc)
    (mulAssociative ql qr qc)
    (mulAssociative bl br bc)
    (mergeNumeratorAssociative
      pl bl tl pr br tr qc bc tc)

-- Structural tree gives total recursion independently of
-- n and floor-division termination obligations.
data SplitTree : Set where
  emptyTree : SplitTree
  term : (a b p q : ℤ) → SplitTree
  join : SplitTree → SplitTree → SplitTree

evaluate : SplitTree → SplitNode
evaluate emptyTree = empty
evaluate (term a b p q) = leaf a b p q
evaluate (join left right) = merge (evaluate left) (evaluate right)

treeRotationPreservesEvaluation :
  (A B C : SplitTree) →
  evaluate (join (join A B) C) ≡
  evaluate (join A (join B C))
treeRotationPreservesEvaluation A B C =
  mergeAssociative (evaluate A) (evaluate B) (evaluate C)

------------------------------------------------------------------------
-- Explicit outstanding constructive obligations:
--   * positive b and q leaves -> positive Q*B for nonempty trees
--   * evaluate(T)/(evaluate(Q)*evaluate(B)) = exact finite prefix
--   * original Bishop series prefix equality, Cauchy/tail transport
--   * pinned agda --safe acceptance for this module/import graph.
------------------------------------------------------------------------
