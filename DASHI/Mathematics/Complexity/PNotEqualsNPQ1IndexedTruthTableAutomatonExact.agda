module DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact where

------------------------------------------------------------------------
-- A FINITELY INDEXED, TOTAL SHANNON AUTOMATON ON ALL TRUTH TABLES
--
-- This donor avoids postulating the existence of a Q1 transition target:
-- each arity-r state is an actual Fin index for a Boolean table of length 2^r.
-- The false/true transitions are computed by selecting the corresponding half
-- of the decoded parent table and re-encoding that table.
--
-- Unlike the canonical REACHABLE quotient, this automaton includes every
-- Boolean truth function at every layer. It is therefore an intentionally
-- very large total reference implementation. It establishes finitary indexing
-- and transition correctness, NOT strict resource fit or Q1 admission.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon

------------------------------------------------------------------------
-- Finite state IDs, indexed by remaining input arity.
--
-- There are 2^(2^r) possible r-ary truth tables. This deliberately includes
-- functions not reachable from the selected root, so it does not pretend to
-- be the minimal or charged reachable quotient.
------------------------------------------------------------------------

IndexedState : Nat → Set
IndexedState remaining =
  Fin.Fin
    (Bits.bitCardinality (Bits.bitCardinality remaining))

decodeState :
  ∀ {remaining : Nat} →
  IndexedState remaining →
  Merge.SemanticKey remaining
decodeState =
  Bits.finToBits

encodeState :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  IndexedState remaining
encodeState =
  Bits.bitsToFin

decodeEncodeState :
  ∀ {remaining : Nat}
    (key : Merge.SemanticKey remaining) →
  decodeState (encodeState key) ≡ key
decodeEncodeState =
  Bits.finToBitsAfterBitsToFin

encodeDecodeState :
  ∀ {remaining : Nat}
    (state : IndexedState remaining) →
  encodeState (decodeState state) ≡ state
encodeDecodeState =
  Bits.bitsToFinAfterFinToBits

------------------------------------------------------------------------
-- Actual deterministic total transitions for both Shannon actions.
------------------------------------------------------------------------

indexedStep :
  ∀ {remaining : Nat} →
  Bool →
  IndexedState (suc remaining) →
  IndexedState remaining
indexedStep action parent =
  encodeState
    (Truth.restrictTruthTable action
      (decodeState parent))

indexedStepDecodesToRestrictedKey :
  ∀ {remaining : Nat}
    (action : Bool)
    (parent : IndexedState (suc remaining)) →
  decodeState (indexedStep action parent)
  ≡
  Truth.restrictTruthTable action
    (decodeState parent)
indexedStepDecodesToRestrictedKey action parent =
  decodeEncodeState _

------------------------------------------------------------------------
-- Exact same-root semantic realization.
------------------------------------------------------------------------

indexRestrictionNode :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  IndexedState remaining
indexRestrictionNode node =
  encodeState (Merge.semanticKey node)

indexRestrictionNodeExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (node : Width.LayerNode {root = root} remaining) →
  decodeState (indexRestrictionNode node)
  ≡
  Merge.semanticKey node
indexRestrictionNodeExact node =
  decodeEncodeState _

indexRestrictionNodeStepExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (parent : Width.LayerNode {root = root} (suc remaining)) →
  indexRestrictionNode (Shannon.layerChild action parent)
  ≡
  indexedStep action (indexRestrictionNode parent)
indexRestrictionNodeStepExact action parent =
  cong encodeState
    (trans
      (Merge.semanticKeyShannonStepExact action parent)
      (cong
        (Truth.restrictTruthTable action)
        (sym (indexRestrictionNodeExact parent))))

------------------------------------------------------------------------
-- Identical finite indices imply full future-semantic equality.
------------------------------------------------------------------------

sameIndexedStateImpliesResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  indexRestrictionNode left ≡ indexRestrictionNode right →
  Width.LayerResidualEqual left right
sameIndexedStateImpliesResidualEquality
    {left = left}
    {right = right}
    sameIndex =
  Merge.keyEqualityPreservesFutureSemantics
    (trans
      (sym (indexRestrictionNodeExact left))
      (trans
        (cong decodeState sameIndex)
        (indexRestrictionNodeExact right)))

residualEqualityGivesEqualIndices :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : Width.LayerNode {root = root} remaining} →
  Width.LayerResidualEqual left right →
  indexRestrictionNode left ≡ indexRestrictionNode right
residualEqualityGivesEqualIndices proof =
  cong encodeState (Merge.residualEqualityGivesKeyEquality proof)

------------------------------------------------------------------------
-- TERMINAL LABELS
--
-- Arity zero has one empty input assignment, hence its truth table has
-- exactly one Boolean entry. The label is looked up from that literal entry.
------------------------------------------------------------------------

terminalLabel :
  IndexedState zero →
  Bool
terminalLabel state =
  Vec.lookup
    (decodeState state)
    Fin.zero

------------------------------------------------------------------------
-- The field "terminalLabel" above is data, not an oracle. The missing Q1
-- integration is an actual globally packed state set, reachable filtering,
-- terminal evaluation correspondence, honest interpreter trace, and proof
-- that the resulting graph satisfies the existing strict charged budget.
------------------------------------------------------------------------
