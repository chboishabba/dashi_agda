module DASHI.Mathematics.Complexity.PNotEqualsNPQ1KeyOnlyTransitionExact where

------------------------------------------------------------------------
-- ROOT-REACHABLE SHANNON TRANSITIONS WITHOUT REPRESENTATIVE LOOKUP
--
-- The current canonical state is literally a truth-table key. Its children
-- can be computed directly by choosing the relevant half of that table.
--
-- A finite key search converts this child table to the actual next-layer
-- numeric Fin index. Completeness is proved using rooted enumeration, but
-- evaluation of the TRANSITION does not traverse a restriction-history node.
--
-- This is strictly closer to a runnable quotient automaton than a
-- transition that reconstructs a proof-relevant source representative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalRepresentativeSelectionExact as Rep
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon

------------------------------------------------------------------------
-- Direct lookup from the decoded parent key, without reconstructing a node.
------------------------------------------------------------------------

keyOnlyStep :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState previous) →
  Maybe
    (Σ
      (Reachable.ReachableNumericState (Root.descend previous))
      (λ target →
        Reachable.decodeReachableState
          (Root.descend previous) target
        ≡
        Truth.restrictTruthTable action
          (Reachable.decodeReachableState previous source)))
keyOnlyStep action previous source =
  Search.findKeyCertified
    (Truth.restrictTruthTable action
      (Reachable.decodeReachableState previous source))
    (Root.rootedMergedSemanticKeys (Root.descend previous))

------------------------------------------------------------------------
-- The descendant key exists: use the representative only IN THE PROOF,
-- rather than as a computation required by the machine transition.
------------------------------------------------------------------------

childKeyOccurs :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState previous) →
  Merge.ListedKey
    (Truth.restrictTruthTable action
      (Reachable.decodeReachableState previous source))
    (Root.rootedMergedSemanticKeys (Root.descend previous))
childKeyOccurs action previous source
    with Rep.representativeOfIndex previous source
... | representative =
  subst
    (λ key →
      Merge.ListedKey key
        (Root.rootedMergedSemanticKeys (Root.descend previous)))
    (trans
      (Merge.semanticKeyShannonStepExact
        action
        (Rep.node representative))
      (cong
        (Truth.restrictTruthTable action)
        (Rep.keyMatchesIndex representative)))
    (Merge.canonicalKeysCoverInput
      (Merge.keyForLayer (Root.rootedLayer (Root.descend previous)))
      (Merge.semanticKey
        (Shannon.layerChild action (Rep.node representative)))
      (Reachable.keyForLayerListed
        (Reachable.childListed
          action previous
          (Rep.node representative)
          (Rep.inRootedLayer representative))))

------------------------------------------------------------------------
-- Totality is a theorem about the real finite key-search algorithm.
-- It does NOT say the construction of all those keys meets the Q1 budget.
------------------------------------------------------------------------

keyOnlyStepComplete :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState previous) →
  Σ
    (Σ
      (Reachable.ReachableNumericState (Root.descend previous))
      (λ target →
        Reachable.decodeReachableState (Root.descend previous) target
        ≡
        Truth.restrictTruthTable action
          (Reachable.decodeReachableState previous source)))
    (λ success →
      keyOnlyStep action previous source ≡ just success)
keyOnlyStepComplete action previous source
    with Search.findKeyCertifiedComplete
      (childKeyOccurs action previous source)
... | target , (found , exact) =
  (target , found) , exact

------------------------------------------------------------------------
-- The genuinely operational transition charge is now only:
--
--   (1) decode a finite key by list lookup;
--   (2) restrict a 2^(r+1)-bit table to 2^r bits;
--   (3) search the finite next-layer key list.
--
-- ROOT-LAYER GENERATION, evaluator visits, key deduplication and storage
-- are separate costs that must be counted before any Clay-facing strict fit.
------------------------------------------------------------------------
