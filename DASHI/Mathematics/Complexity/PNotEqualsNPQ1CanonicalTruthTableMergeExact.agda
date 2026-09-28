module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact where

------------------------------------------------------------------------
-- EXECUTABLE FINITE-LAYER SEMANTIC MERGING
--
-- The trace generator gives cheap reachability. Its trace is not a canonical
-- semantic key: distinct traces can compute identical residual functions.
--
-- Here the finite truth-table repair is used as an exact semantic key.
-- A structural equality decision merges equal keys in a concrete finite list.
--
-- The scan cost is recorded explicitly. No claim is made that this constructs
-- a globally admitted Q1 transition table within the direct-DP strict budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth

------------------------------------------------------------------------
-- Decidable equality of finite Bool tables, with no function extensionality.
------------------------------------------------------------------------

decideBoolEqual :
  (left right : Bool) →
  (left ≡ right) ⊎ (left ≡ right → ⊥)
decideBoolEqual false false = inj₁ refl
decideBoolEqual false true = inj₂ (λ ())
decideBoolEqual true false = inj₂ (λ ())
decideBoolEqual true true = inj₁ refl

decideTableEqual :
  ∀ {n : Nat} →
  (left right : Vec.Vec Bool n) →
  (left ≡ right) ⊎ (left ≡ right → ⊥)
decideTableEqual Vec.[] Vec.[] = inj₁ refl
decideTableEqual (left Vec.∷ lefts) (right Vec.∷ rights)
    with decideBoolEqual left right
... | inj₂ notSame = inj₂ (λ { refl → notSame refl })
... | inj₁ refl with decideTableEqual lefts rights
...   | inj₁ refl = inj₁ refl
...   | inj₂ notSame = inj₂ (λ { refl → notSame refl })

------------------------------------------------------------------------
-- Canonicalized fixed-layer semantic keys.
------------------------------------------------------------------------

SemanticKey : Nat → Set
SemanticKey remaining =
  Vec.Vec Bool (Bits.bitCardinality remaining)

semanticKey :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  SemanticKey remaining
semanticKey = Truth.truthTableRepair

keyEqualityPreservesFutureSemantics :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  semanticKey left ≡ semanticKey right →
  Width.LayerResidualEqual left right
keyEqualityPreservesFutureSemantics =
  Truth.truthTableRepairEqualityImpliesResidualEquality

------------------------------------------------------------------------
-- Real insertion / deduplication, not a supplied equivalence oracle.
------------------------------------------------------------------------

insertSemanticKey :
  ∀ {remaining : Nat} →
  SemanticKey remaining →
  List (SemanticKey remaining) →
  List (SemanticKey remaining)
insertSemanticKey key [] = key ∷ []
insertSemanticKey key (head ∷ rest)
    with decideTableEqual key head
... | inj₁ same = head ∷ rest
... | inj₂ different =
  head ∷ insertSemanticKey key rest

canonicalKeyList :
  ∀ {remaining : Nat} →
  List (SemanticKey remaining) →
  List (SemanticKey remaining)
canonicalKeyList [] = []
canonicalKeyList (key ∷ rest) =
  insertSemanticKey key (canonicalKeyList rest)

keyForLayer :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} remaining) →
  List (SemanticKey remaining)
keyForLayer [] = []
keyForLayer (node ∷ rest) =
  semanticKey node ∷ keyForLayer rest

canonicalMergedLayer :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} remaining) →
  List (SemanticKey remaining)
canonicalMergedLayer nodes =
  canonicalKeyList (keyForLayer nodes)

------------------------------------------------------------------------
-- Explicit comparison work. These are TABLE comparisons, each requiring
-- inspection of up to 2^remaining bits. Count both the number of calls and
-- a conservative full-width charge for each call.
------------------------------------------------------------------------

insertComparisonCount :
  ∀ {remaining : Nat} →
  SemanticKey remaining →
  List (SemanticKey remaining) →
  Nat
insertComparisonCount key [] = zero
insertComparisonCount key (head ∷ rest)
    with decideTableEqual key head
... | inj₁ same = suc zero
... | inj₂ different =
  suc (insertComparisonCount key rest)

canonicalComparisonCount :
  ∀ {remaining : Nat} →
  List (SemanticKey remaining) →
  Nat
canonicalComparisonCount [] = zero
canonicalComparisonCount (key ∷ rest) =
  insertComparisonCount key (canonicalKeyList rest)
  + canonicalComparisonCount rest

fullWidthComparisonBudget :
  ∀ {remaining : Nat} →
  List (SemanticKey remaining) →
  Nat
fullWidthComparisonBudget {remaining} keys =
  Bits.bitCardinality remaining
  * canonicalComparisonCount keys

------------------------------------------------------------------------
-- Source materialization cost is separate from merging comparisons.
-- Constructing a literal table for one node evaluates 2^remaining rows.
------------------------------------------------------------------------

layerKeyMaterializationRows :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} remaining) →
  Nat
layerKeyMaterializationRows {remaining = remaining} [] =
  zero
layerKeyMaterializationRows {remaining = remaining} (_ ∷ rest) =
  Bits.bitCardinality remaining
  + layerKeyMaterializationRows rest

layerTotalAccounting :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  List (Width.LayerNode {root = root} remaining) →
  Nat
layerTotalAccounting nodes =
  layerKeyMaterializationRows nodes
  + fullWidthComparisonBudget (keyForLayer nodes)

------------------------------------------------------------------------
-- The finite list above is only a same-layer set of semantic keys. A real Q1
-- automaton still needs cross-layer state numbering, both transition targets,
-- terminal labels, a construction execution trace, and its combined strict
-- resource charge on the actual candidate-quoted root.
------------------------------------------------------------------------
