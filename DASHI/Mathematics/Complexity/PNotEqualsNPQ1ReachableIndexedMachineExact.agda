module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableIndexedMachineExact where

------------------------------------------------------------------------
-- NUMERIC-STATE-ONLY SHANNON TRANSITIONS ON THE REACHABLE QUOTIENT
--
-- This owner closes the "hidden representative argument" defect.
-- Input: one canonical Fin state ID at the current ROOTED layer.
--
-- Procedure:
--   1. recover an actual source restriction node via finite-key provenance;
--   2. take its literal Shannon child;
--   3. structurally search the next layer's canonical key list;
--   4. return a Fin index together with its exact future-semantic equality.
--
-- Every indexed state is represented by a real rooted node; the enumerator
-- contains its children; so the certified lookup cannot fail.
--
-- No operational polynomial bound or strict Q1 budget success is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalRepresentativeSelectionExact as Rep
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth

------------------------------------------------------------------------
-- Right congruence makes a representative's computed child independent of
-- the chosen restriction history, at the level of the canonical table key.
------------------------------------------------------------------------

childIndexSemanticReceipt :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (index : Reachable.ReachableNumericState previous)
    (rep : Rep.NumericRepresentative previous index)
    (target : Reachable.ReachableNumericState (Root.descend previous)) →
  Reachable.decodeReachableState (Root.descend previous) target
    ≡ Merge.semanticKey
      (Shannon.layerChild action (Rep.node rep)) →
  Reachable.decodeReachableState (Root.descend previous) target
    ≡ Truth.restrictTruthTable action
      (Reachable.decodeReachableState previous index)
childIndexSemanticReceipt action previous index rep target found =
  trans
    found
    (trans
      (Merge.semanticKeyShannonStepExact
        action
        (Rep.node rep))
      (cong
        (Truth.restrictTruthTable action)
        (Rep.keyMatchesIndex rep)))

------------------------------------------------------------------------
-- Output type carries the exact transition semantics on its finite index.
------------------------------------------------------------------------

IndexedSuccessor :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (index : Reachable.ReachableNumericState previous) →
  Set
IndexedSuccessor action previous index =
  Σ
    (Reachable.ReachableNumericState (Root.descend previous))
    (λ target →
      Reachable.decodeReachableState (Root.descend previous) target
      ≡
      Truth.restrictTruthTable action
        (Reachable.decodeReachableState previous index))

reachableIndexedStep :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (index : Reachable.ReachableNumericState previous) →
  Maybe (IndexedSuccessor action previous index)
reachableIndexedStep action previous index
    with Rep.representativeOfIndex previous index
... | rep
    with Search.findKeyCertified
      (Merge.semanticKey (Shannon.layerChild action (Rep.node rep)))
      (Root.rootedMergedSemanticKeys (Root.descend previous))
...   | nothing = nothing
...   | just (target , found) =
  just
    (target ,
      childIndexSemanticReceipt
        action previous index rep target found)

------------------------------------------------------------------------
-- Every canonical index comes from the rooted layer, and the rooted child
-- enumeration covers both Shannon branches. Hence scanner success is
-- derivable, not assumed.
------------------------------------------------------------------------

reachableIndexedStepComplete :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (index : Reachable.ReachableNumericState previous) →
  Σ
    (IndexedSuccessor action previous index)
    (λ successor →
      reachableIndexedStep action previous index ≡ just successor)
reachableIndexedStepComplete action previous index
    with Rep.representativeOfIndex previous index
... | rep
    with Search.findKeyCertifiedComplete
      (Merge.canonicalKeysCoverInput
        (Merge.keyForLayer
          (Root.rootedLayer (Root.descend previous)))
        (Merge.semanticKey
          (Shannon.layerChild action (Rep.node rep)))
        (Reachable.keyForLayerListed
          (Reachable.childListed
            action previous (Rep.node rep) (Rep.inRootedLayer rep))))
...   | target , (found , successful)
      rewrite successful =
  (target ,
    childIndexSemanticReceipt
      action previous index rep target found)
  ,
  refl

------------------------------------------------------------------------
-- In particular, an arity-positive canonical numerical state has a
-- deterministically computable child. This is an existence-and-correctness
-- theorem about the *unbudgeted* finite reachable quotient, not first-step
-- success of the Clay-critical charged Q1 state constructor.
------------------------------------------------------------------------
