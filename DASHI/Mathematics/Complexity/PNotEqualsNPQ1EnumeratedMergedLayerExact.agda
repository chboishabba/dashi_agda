module DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact where

------------------------------------------------------------------------
-- ACTUAL ONE-LAYER SHANNON ENUMERATION AND CANONICAL MERGING
--
-- This is the first executable bridge from a finite parent-layer list to
-- all of its literal children. No list is supplied as a magic "all states"
-- oracle: expansion is constructed by running both actual Shannon children
-- for every parent.
--
-- Canonical semantic keys and their comparison/materialization charges are
-- computed from those children using the existing finite-key builder.
--
-- This does NOT yet allocate globally numbered Q1 states, or claim the direct
-- DP strict budget is met.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge

------------------------------------------------------------------------
-- Construct a complete child list for each supplied parent-layer list.
------------------------------------------------------------------------

enumerateShannonChildren :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} (suc remaining)) →
  List (Width.LayerNode {root = root} remaining)
enumerateShannonChildren [] =
  []
enumerateShannonChildren (parent ∷ rest) =
  Shannon.falseLayerChild parent
  ∷ Shannon.trueLayerChild parent
  ∷ enumerateShannonChildren rest

twice : Nat → Nat
twice zero = zero
twice (suc count) = suc (suc (twice count))

enumeratedChildCount :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (parents : List (Width.LayerNode {root = root} (suc remaining))) →
  length (enumerateShannonChildren parents)
  ≡
  twice (length parents)
enumeratedChildCount [] =
  refl
enumeratedChildCount (parent ∷ rest)
    rewrite enumeratedChildCount rest =
  refl

------------------------------------------------------------------------
-- The actual merged child layer and explicit semantic-key work.
------------------------------------------------------------------------

enumerateAndMergeChildren :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} (suc remaining)) →
  List (Merge.SemanticKey remaining)
enumerateAndMergeChildren parents =
  Merge.canonicalMergedLayer
    (enumerateShannonChildren parents)

oneLayerEnumerationWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} (suc remaining)) →
  Nat
oneLayerEnumerationWork parents =
  twice (length parents)

oneLayerKeyWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} (suc remaining)) →
  Nat
oneLayerKeyWork parents =
  Merge.layerTotalAccounting
    (enumerateShannonChildren parents)

oneLayerDeclaredWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} (suc remaining)) →
  Nat
oneLayerDeclaredWork parents =
  oneLayerEnumerationWork parents
  + oneLayerKeyWork parents

oneLayerWorkDecomposition :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (parents : List (Width.LayerNode {root = root} (suc remaining))) →
  oneLayerDeclaredWork parents
  ≡
  oneLayerEnumerationWork parents
  + oneLayerKeyWork parents
oneLayerWorkDecomposition parents =
  refl

------------------------------------------------------------------------
-- Full-graph accounting still requires global state allocation, transition
-- targets, terminal correctness, constructor execution and strict fit.
--
-- In particular the rows/bit comparisons counted by Merge are a declaration
-- of high-level operations, not a machine-step upper bound for unrestricted
-- formula evaluation. No polynomial-time claim follows.
------------------------------------------------------------------------
