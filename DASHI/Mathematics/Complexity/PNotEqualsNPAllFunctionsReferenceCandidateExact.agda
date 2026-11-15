module DASHI.Mathematics.Complexity.PNotEqualsNPAllFunctionsReferenceCandidateExact where

------------------------------------------------------------------------
-- ALL-FUNCTIONS REFERENCE GRAPH -> ACTUAL TRANSITION TABLE CANDIDATE
--
-- This is the first fully explicit flat TransitionTableCandidate built from
-- the existing indexed Shannon reference machine.
--
-- It is intentionally enormous and therefore NOT expected to satisfy the Clay
-- charged budget. Its role is different:
--
--   * prove the table/admission compiler is constructible;
--   * make semantic failure impossible by construction;
--   * leave resource exhaustion as the explicit reason this baseline can stop.
--
-- Terminal states self-loop only because TransitionTableCandidate has a total
-- Bool transition field. Reachable RestrictionDerivations never take another
-- Shannon action after arity zero, so those self-loops carry no semantic role.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_<_)
import Data.Fin.Base as FinBase
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeAdmissionExact as Tree
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedIndexedReferenceMachineExact as Packed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact as Graph
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1NumericIndexedGraphExact as Numeric
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon

------------------------------------------------------------------------
-- Totalized global numeric transition.
------------------------------------------------------------------------

referenceStep :
  ∀ {bound : Nat} →
  Bool →
  Numeric.NumericState bound →
  Numeric.NumericState bound
referenceStep action state
    with Numeric.numericDecode state
... | Packed.packed FinBase.zero table =
  state
... | Packed.packed (FinBase.suc remaining) table =
  Numeric.numericEncode
    (Packed.packed remaining
      (Indexed.indexedStep action table))

------------------------------------------------------------------------
-- One actual TransitionTableCandidate for any root.
------------------------------------------------------------------------

allFunctionsCandidate :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Candidate.TransitionTableCandidate root
allFunctionsCandidate {rootVariables} root =
  Candidate.transition-table-candidate
    (length (Graph.allPackedStates rootVariables))
    (Numeric.numericEncode
      (Packed.rootPackedState root))
    (λ state action →
      referenceStep action state)

------------------------------------------------------------------------
-- Arity is literally the packed state's tag.
------------------------------------------------------------------------

referenceStateArity :
  ∀ {bound : Nat} →
  Numeric.NumericState bound →
  Nat
referenceStateArity state
    with Numeric.numericDecode state
... | Packed.packed remaining table =
  FinBase.toℕ remaining

zeroNotSuccessor :
  ∀ {n : Nat} →
  zero ≡ suc n →
  ⊥
zeroNotSuccessor ()

successorInjective :
  ∀ {left right : Nat} →
  suc left ≡ suc right →
  left ≡ right
successorInjective refl =
  refl

referenceRootArityExact :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  referenceStateArity
    (Candidate.rootState
      (allFunctionsCandidate root))
  ≡
  rootVariables
referenceRootArityExact root
    rewrite
      Numeric.numericDecodeEncode
        (Packed.rootPackedState root) =
  refl

referenceStepArityExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (state :
      Fin
        (Candidate.stateCount
          (allFunctionsCandidate root)))
    (remaining : Nat) →
  referenceStateArity state ≡ suc remaining →
  referenceStateArity
      (Candidate.step
        (allFunctionsCandidate root)
        state
        action)
  ≡
  remaining
referenceStepArityExact action state remaining arityExact
    with Numeric.numericDecode state
... | Packed.packed FinBase.zero table =
  ⊥-elim (zeroNotSuccessor arityExact)
... | Packed.packed (FinBase.suc lower) table
    rewrite
      Numeric.numericDecodeEncode
        (Packed.packed lower
          (Indexed.indexedStep action table)) =
  successorInjective arityExact

------------------------------------------------------------------------
-- Terminal labels are literal decoded truth-table labels.
------------------------------------------------------------------------

referenceTerminalLabel :
  ∀ {bound : Nat} →
  Numeric.NumericState bound →
  Bool
referenceTerminalLabel state
    with Numeric.numericDecode state
... | Packed.packed FinBase.zero table =
  Indexed.terminalLabel table
... | Packed.packed (FinBase.suc remaining) table =
  false

------------------------------------------------------------------------
-- Finite verification tree over actual restriction nodes.
------------------------------------------------------------------------

referenceTreeForLayer :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (layer : Width.LayerNode {root = root} remaining)
    (tag : FinBase.Fin (suc rootVariables)) →
  FinBase.toℕ tag ≡ remaining →
  Tree.TerminalVerificationTree
    (allFunctionsCandidate root)
    referenceTerminalLabel
    (Family.currentFormula (Width.node layer))
    (Numeric.numericEncode
      (Packed.packed tag
        (Indexed.indexRestrictionNode layer)))
referenceTreeForLayer {remaining = zero}
    layer@(Width.layer-node
      (Family.restriction-node .zero current derivation)
      refl)
    FinBase.zero
    refl
    rewrite
      Numeric.numericDecodeEncode
        (Packed.packed FinBase.zero
          (Indexed.indexRestrictionNode layer)) =
  Tree.terminalLeaf
    (Indexed.indexedTerminalLabelCorrect layer)
referenceTreeForLayer {remaining = zero}
    (Width.layer-node
      (Family.restriction-node .zero current derivation)
      refl)
    (FinBase.suc tag)
    tagExact =
  ⊥-elim (zeroNotSuccessor (sym tagExact))
referenceTreeForLayer {remaining = suc remaining}
    (Width.layer-node
      (Family.restriction-node .(suc remaining) current derivation)
      refl)
    FinBase.zero
    tagExact =
  ⊥-elim (zeroNotSuccessor tagExact)
referenceTreeForLayer {remaining = suc remaining}
    layer@(Width.layer-node
      (Family.restriction-node .(suc remaining) current derivation)
      refl)
    (FinBase.suc tag)
    tagExact
    rewrite
      Numeric.numericDecodeEncode
        (Packed.packed (FinBase.suc tag)
          (Indexed.indexRestrictionNode layer))
    | Indexed.indexRestrictionNodeStepExact false layer
    | Indexed.indexRestrictionNodeStepExact true layer =
  Tree.branch
    (referenceTreeForLayer
      (Shannon.layerChild false layer)
      tag
      (successorInjective tagExact))
    (referenceTreeForLayer
      (Shannon.layerChild true layer)
      tag
      (successorInjective tagExact))

referenceTerminalVerificationTree :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Tree.TerminalVerificationTree
    (allFunctionsCandidate root)
    referenceTerminalLabel
    root
    (Candidate.rootState
      (allFunctionsCandidate root))
referenceTerminalVerificationTree {rootVariables} root =
  referenceTreeForLayer
    (Root.rootLayerNode root)
    (FinBase.fromℕ rootVariables)
    refl

------------------------------------------------------------------------
-- Full finite tree/local-arity admission.
------------------------------------------------------------------------

allFunctionsTreeAdmission :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Tree.TreeLocalArityTerminalAdmission
    (allFunctionsCandidate root)
allFunctionsTreeAdmission root =
  Tree.tree-local-arity-terminal-admission
    referenceStateArity
    (referenceRootArityExact root)
    (referenceStepArityExact false)
    (referenceStepArityExact true)
    referenceTerminalLabel
    (referenceTerminalVerificationTree root)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- A completely explicit flat table + finite semantic admission exists for
-- every root with no SAT oracle and no arbitrary semantic theorem.
--
-- It is the all-functions graph, so its size is intentionally enormous. The
-- remaining Clay question is entirely quantitative/structural: replace this
-- reference table by a root-reachable implementation whose construction,
-- evaluation and next-state payload fit the candidate-coupled recursive budget.
------------------------------------------------------------------------
