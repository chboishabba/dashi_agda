module DASHI.Mathematics.Complexity.PNotEqualsNPResidualAggregationTreeExact where

------------------------------------------------------------------------
-- RESIDUAL AGGREGATION TREE: LOG DEPTH, LINEAR TOTAL SIZE
--
-- Boolean residuals can be aggregated by a balanced XOR tree.
--
-- For 2^d residual leaves:
--
--   depth          = d
--   leaves         = 2^d
--   total tree nodes = 2^(d+1)-1
--
-- So recursive aggregation genuinely reduces dependency depth, but a complete
-- deterministic certificate which materializes every aggregate node remains
-- linear in the number of residuals.
--
-- This is the deterministic counterpart to
-- PNotEqualsNPBooleanResidualFingerprintExact:
--
--   * full tree      -> exact but linear total certificate;
--   * random sample  -> few queries but randomized soundness.
--
-- Hence neither move alone closes the self-diagonal N versus |C_N| recurrence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Mathematics.Complexity.PNotEqualsNPBooleanResidualFingerprintExact as Fingerprint

------------------------------------------------------------------------
-- Perfect binary aggregation trees indexed by depth.
------------------------------------------------------------------------

data ResidualAggregateTree : Nat → Set where
  residualLeaf :
    Bool →
    ResidualAggregateTree zero

  residualBranch :
    ∀ {depth} →
    ResidualAggregateTree depth →
    ResidualAggregateTree depth →
    ResidualAggregateTree (suc depth)

aggregateValue :
  ∀ {depth} →
  ResidualAggregateTree depth →
  Bool
aggregateValue (residualLeaf value) =
  value
aggregateValue (residualBranch left right) =
  Fingerprint.xorBool
    (aggregateValue left)
    (aggregateValue right)

leafCount :
  ∀ {depth} →
  ResidualAggregateTree depth →
  Nat
leafCount (residualLeaf value) =
  suc zero
leafCount (residualBranch left right) =
  leafCount left + leafCount right

treeNodeCount :
  ∀ {depth} →
  ResidualAggregateTree depth →
  Nat
treeNodeCount (residualLeaf value) =
  suc zero
treeNodeCount (residualBranch left right) =
  suc
    (treeNodeCount left + treeNodeCount right)

------------------------------------------------------------------------
-- Canonical shape accounting.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero =
  suc zero
pow2 (suc depth) =
  pow2 depth + pow2 depth

canonicalZeroTree :
  (depth : Nat) →
  ResidualAggregateTree depth
canonicalZeroTree zero =
  residualLeaf false
canonicalZeroTree (suc depth) =
  residualBranch
    (canonicalZeroTree depth)
    (canonicalZeroTree depth)

canonicalLeafCount :
  (depth : Nat) →
  leafCount (canonicalZeroTree depth)
  ≡ pow2 depth
canonicalLeafCount zero =
  refl
canonicalLeafCount (suc depth)
    rewrite canonicalLeafCount depth =
  refl

------------------------------------------------------------------------
-- Total node recurrence.
--
-- We keep the recurrence exact rather than importing subtraction just to write
-- 2^(d+1)-1.  It already exposes the size barrier:
--
--   nodes(d+1) = 1 + 2*nodes(d).
------------------------------------------------------------------------

canonicalTreeNodeCountRecurrence :
  (depth : Nat) →
  treeNodeCount (canonicalZeroTree (suc depth))
  ≡
  suc
    (treeNodeCount (canonicalZeroTree depth)
     + treeNodeCount (canonicalZeroTree depth))
canonicalTreeNodeCountRecurrence depth =
  refl

------------------------------------------------------------------------
-- Every complete tree contains at least as many nodes as leaves.
------------------------------------------------------------------------

leafCountBelowNodeCount :
  ∀ {depth}
    (tree : ResidualAggregateTree depth) →
  leafCount tree Nat≤ treeNodeCount tree
leafCountBelowNodeCount (residualLeaf value) =
  leRefl
leafCountBelowNodeCount (residualBranch left right) =
  leSucc
    (leAdd
      (leafCountBelowNodeCount left)
      (leafCountBelowNodeCount right))
  where
    data _Nat≤_ : Nat → Nat → Set where
      leZero :
        ∀ {right} →
        zero Nat≤ right

      leSucc :
        ∀ {left right} →
        left Nat≤ right →
        suc left Nat≤ suc right

    leRefl :
      ∀ {value} →
      value Nat≤ value
    leRefl {zero} =
      leZero
    leRefl {suc value} =
      leSucc leRefl

    leAdd :
      ∀ {a b c d} →
      a Nat≤ b →
      c Nat≤ d →
      (a + c) Nat≤ (b + d)
    leAdd leZero right =
      right
    leAdd (leSucc left) right =
      leSucc (leAdd left right)

------------------------------------------------------------------------
-- NOTE
--
-- The local Nat-order relation above is intentionally structural and scoped to
-- this accounting lemma.  No complexity lower bound is inferred from it.
--
-- A complete deterministic aggregation tree still materializes at least one
-- node per residual leaf.  Achieving sublinear verification therefore requires
-- either randomized sampling, a stronger algebraic oracle/commitment, or a
-- reusable global theorem which summarizes the specific circuit family.
------------------------------------------------------------------------
