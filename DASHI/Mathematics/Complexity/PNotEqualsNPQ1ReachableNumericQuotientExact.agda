module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact where

------------------------------------------------------------------------
-- ACTUAL ROOT-REACHABLE, CANONICALLY MERGED NUMERIC QUOTIENT
--
-- Unlike the all-truth-functions reference machine, each state index belongs
-- to the finite list of *root-reachable* canonical residual truth-table keys.
--
-- A witness that a particular Shannon restriction is reachable is preserved
-- through root-generated layer enumeration and finite-key deduplication.
-- Each node therefore gets a literal Fin index and exact decoded semantics.
-- Both child indices are extracted from the enumerated next layer: no
-- existence of transition targets is postulated.
--
-- The quotient here has a typed arity-graded index. Packing all layers into
-- one serial state table, actual machine-step charging, and strict Q1
-- construction admission are separate debts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth

------------------------------------------------------------------------
-- A listed restriction has a listed semantic key; this is independent of
-- equality of proof-relevant restriction histories.
------------------------------------------------------------------------

keyForLayerListed :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {node : Width.LayerNode {root = root} remaining}
    {nodes : List (Width.LayerNode {root = root} remaining)} →
  Step.Listed node nodes →
  Merge.ListedKey
    (Merge.semanticKey node)
    (Merge.keyForLayer nodes)
keyForLayerListed Step.first =
  Merge.firstKey
keyForLayerListed (Step.later witness) =
  Merge.laterKey (keyForLayerListed witness)

------------------------------------------------------------------------
-- A real numeric index into exactly the canonical root-reachable layer.
------------------------------------------------------------------------

lookupKey :
  ∀ {remaining : Nat}
    (keys : List (Merge.SemanticKey remaining)) →
  Fin.Fin (length keys) →
  Merge.SemanticKey remaining
lookupKey [] ()
lookupKey (head ∷ tail) Fin.zero = head
lookupKey (head ∷ tail) (Fin.suc index) =
  lookupKey tail index

indexOfListedKey :
  ∀ {remaining : Nat}
    {key : Merge.SemanticKey remaining}
    {keys : List (Merge.SemanticKey remaining)} →
  Merge.ListedKey key keys →
  Fin.Fin (length keys)
indexOfListedKey Merge.firstKey =
  Fin.zero
indexOfListedKey (Merge.laterKey proof) =
  Fin.suc (indexOfListedKey proof)

indexOfListedKeyExact :
  ∀ {remaining : Nat}
    {key : Merge.SemanticKey remaining}
    {keys : List (Merge.SemanticKey remaining)}
    (proof : Merge.ListedKey key keys) →
  lookupKey keys (indexOfListedKey proof) ≡ key
indexOfListedKeyExact Merge.firstKey =
  refl
indexOfListedKeyExact (Merge.laterKey proof) =
  indexOfListedKeyExact proof

ReachableNumericState :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Root.DescentPath root remaining →
  Set
ReachableNumericState path =
  Fin.Fin (length (Root.rootedMergedSemanticKeys path))

decodeReachableState :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining) →
  ReachableNumericState path →
  Merge.SemanticKey remaining
decodeReachableState path =
  lookupKey (Root.rootedMergedSemanticKeys path)

------------------------------------------------------------------------
-- Actual reachable-node indexing via list membership and deduplication.
------------------------------------------------------------------------

indexReachableNode :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (node : Width.LayerNode {root = root} remaining) →
  Step.Listed node (Root.rootedLayer path) →
  ReachableNumericState path
indexReachableNode path node member =
  indexOfListedKey
    (Merge.canonicalKeysCoverInput
      (Merge.keyForLayer (Root.rootedLayer path))
      (Merge.semanticKey node)
      (keyForLayerListed member))

indexReachableNodeExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (node : Width.LayerNode {root = root} remaining)
    (member : Step.Listed node (Root.rootedLayer path)) →
  decodeReachableState path
    (indexReachableNode path node member)
  ≡
  Merge.semanticKey node
indexReachableNodeExact path node member =
  indexOfListedKeyExact
    (Merge.canonicalKeysCoverInput
      (Merge.keyForLayer (Root.rootedLayer path))
      (Merge.semanticKey node)
      (keyForLayerListed member))

------------------------------------------------------------------------
-- All transitions are on the actual next ROOT-GENERATED layer.
------------------------------------------------------------------------

childListed :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (parent : Width.LayerNode {root = root} (suc remaining)) →
  Step.Listed parent (Root.rootedLayer previous) →
  Step.Listed
    (Shannon.layerChild action parent)
    (Root.rootedLayer (Root.descend previous))
childListed false previous parent member =
  Step.falseChildEnumerated parent (Root.rootedLayer previous) member
childListed true previous parent member =
  Step.trueChildEnumerated parent (Root.rootedLayer previous) member

reachableNumericStep :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (parent : Width.LayerNode {root = root} (suc remaining))
    (member : Step.Listed parent (Root.rootedLayer previous)) →
  ReachableNumericState (Root.descend previous)
reachableNumericStep action previous parent member =
  indexReachableNode
    (Root.descend previous)
    (Shannon.layerChild action parent)
    (childListed action previous parent member)

reachableNumericStepExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (previous : Root.DescentPath root (suc remaining))
    (parent : Width.LayerNode {root = root} (suc remaining))
    (member : Step.Listed parent (Root.rootedLayer previous)) →
  decodeReachableState
    (Root.descend previous)
    (reachableNumericStep action previous parent member)
  ≡
  Truth.restrictTruthTable action
    (decodeReachableState previous
      (indexReachableNode previous parent member))
reachableNumericStepExact action previous parent member =
  trans
    (indexReachableNodeExact
      (Root.descend previous)
      (Shannon.layerChild action parent)
      (childListed action previous parent member))
    (trans
      (Merge.semanticKeyShannonStepExact action parent)
      (cong (Truth.restrictTruthTable action)
        (sym (indexReachableNodeExact previous parent member))))

------------------------------------------------------------------------
-- Root belongs to the initial enumerated layer by computation.
------------------------------------------------------------------------

rootNumericState :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  ReachableNumericState
    (Root.atRoot {root = root})
rootNumericState root =
  indexReachableNode
    Root.atRoot
    (Root.rootLayerNode root)
    Step.first

rootNumericStateExact :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  decodeReachableState
    Root.atRoot
    (rootNumericState root)
  ≡
  Merge.semanticKey (Root.rootLayerNode root)
rootNumericStateExact root =
  indexReachableNodeExact
    Root.atRoot
    (Root.rootLayerNode root)
    Step.first

------------------------------------------------------------------------
-- FRONTIER: the numeric state/transition receipt is fully root-reachable,
-- not the all-functions supergraph. However reachableNumericStep takes a
-- source node plus reachability certificate. The next genuine algorithmic
-- obligation is to choose and store one representative per canonical key,
-- making the transition a function of the numeric ID alone, then charge
-- that representative-selection/execution algorithm operationally.
------------------------------------------------------------------------
