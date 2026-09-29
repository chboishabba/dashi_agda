module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact where

------------------------------------------------------------------------
-- EXECUTABLE LOOKUP INTO ACTUAL ROOT-REACHABLE QUOTIENT LAYERS
--
-- This is the algorithmic strengthening of ReachableNumericQuotientExact:
-- numeric IDs are returned by a concrete structural key comparison scan.
-- A missing key returns nothing; membership from real root enumeration proves
-- the sought keys ARE found. Neither membership nor cost is an oracle.
--
-- This does not yet establish a complete charged Q1 compiler or independent
-- success at the candidate-quoted root.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Fin.Base as Fin
import Data.List.Base
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable

------------------------------------------------------------------------
-- Linear structural-key lookup, returning a real Fin index on success.
------------------------------------------------------------------------

findKeyIndex :
  ∀ {remaining : Nat} →
  (query : Merge.SemanticKey remaining) →
  (keys : List (Merge.SemanticKey remaining)) →
  Maybe (Fin.Fin (Data.List.Base.length keys))
findKeyIndex query [] = nothing
findKeyIndex query (head ∷ tail)
    with Merge.decideTableEqual query head
... | inj₁ same = just Fin.zero
... | inj₂ different with findKeyIndex query tail
...   | nothing = nothing
...   | just index = just (Fin.suc index)

------------------------------------------------------------------------
-- The small arithmetic wrapper above is definitionally zero + length.
-- Use the exact canonical finite index carrier in the public bridge.
------------------------------------------------------------------------

findKeyIndexExact :
  ∀ {remaining : Nat} →
  (query : Merge.SemanticKey remaining) →
  (keys : List (Merge.SemanticKey remaining)) →
  Maybe (Fin.Fin (Data.List.Base.length keys))
findKeyIndexExact = findKeyIndex

findKeyIndexComplete :
  ∀ {remaining : Nat}
    {query : Merge.SemanticKey remaining}
    {keys : List (Merge.SemanticKey remaining)} →
  Merge.ListedKey query keys →
  Σ
    (Fin.Fin (Data.List.Base.length keys))
    (λ index →
      findKeyIndexExact query keys ≡ just index)
findKeyIndexComplete {query = query} {keys = .(query ∷ _)}
    Merge.firstKey
    with Merge.decideTableEqual query query
... | inj₁ same = Fin.zero , refl
... | inj₂ different = ⊥-elim (different refl)
findKeyIndexComplete {query = query} {keys = head ∷ tail}
    (Merge.laterKey member)
    with Merge.decideTableEqual query head
... | inj₁ same = Fin.zero , refl
... | inj₂ different
    with findKeyIndexComplete member
...   | index , exact
      rewrite exact =
        Fin.suc index , refl

findKeyIndexSound :
  ∀ {remaining : Nat}
    (query : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining))
    (index : Fin.Fin (Data.List.Base.length keys)) →
  findKeyIndexExact query keys ≡ just index →
  Reachable.lookupKey keys index ≡ query
findKeyIndexSound query [] () result
findKeyIndexSound query (head ∷ tail) index result
    with Merge.decideTableEqual query head
... | inj₁ same
    with index | result
...   | Fin.zero | refl = sym same
... | inj₂ different
    with findKeyIndexExact query tail
...   | nothing with result
...     | ()
...   | just earlier
    with index | result
...     | Fin.suc target | refl =
      findKeyIndexSound query tail earlier refl

------------------------------------------------------------------------
-- Literal scan work, excluding the Boolean-table comparison width.
------------------------------------------------------------------------

findKeyComparisonCount :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  List (Merge.SemanticKey remaining) →
  Nat
findKeyComparisonCount query [] = zero
findKeyComparisonCount query (head ∷ tail)
    with Merge.decideTableEqual query head
... | inj₁ same = suc zero
... | inj₂ different =
  suc (findKeyComparisonCount query tail)

findKeyFullWidthCharge :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  List (Merge.SemanticKey remaining) →
  Nat
findKeyFullWidthCharge {remaining = remaining} query keys =
  Bits.bitCardinality remaining *
  findKeyComparisonCount query keys

------------------------------------------------------------------------
-- Executable search of both Shannon successors in their ROOTED merged layer.
------------------------------------------------------------------------

findReachableChild :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (parent : Width.LayerNode {root = root} (suc remaining)) →
  Maybe
    (Reachable.ReachableNumericState
      (Root.descend previous))
findReachableChild action previous parent =
  findKeyIndexExact
    (Merge.semanticKey (Shannon.layerChild action parent))
    (Root.rootedMergedSemanticKeys (Root.descend previous))

findReachableChildComplete :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (parent : Width.LayerNode {root = root} (suc remaining))
    (member : Step.Listed parent (Root.rootedLayer previous)) →
  Σ
    (Reachable.ReachableNumericState (Root.descend previous))
    (λ index →
      findReachableChild action previous parent ≡ just index)
findReachableChildComplete action previous parent member =
  findKeyIndexComplete
    (Merge.canonicalKeysCoverInput
      (Merge.keyForLayer
        (Root.rootedLayer (Root.descend previous)))
      (Merge.semanticKey (Shannon.layerChild action parent))
      (Reachable.keyForLayerListed
        (Reachable.childListed action previous parent member)))

------------------------------------------------------------------------
-- This is real finite search, not a supplied child-ID function. The next
-- step must prove source-index-only transition factorization by selecting a
-- representative for each canonical key, and explicitly account for finding
-- that representative plus root formula evaluation.
------------------------------------------------------------------------
