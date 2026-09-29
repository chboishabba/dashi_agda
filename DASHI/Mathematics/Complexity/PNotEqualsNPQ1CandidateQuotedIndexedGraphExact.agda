module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CandidateQuotedIndexedGraphExact where

------------------------------------------------------------------------
-- SAME-OBJECT CANDIDATE ROOT -> EXPLICIT INDEXED GRAPH
--
-- The indexed reference graph and its budget gate are instantiated on the
-- EXACT Cook formula of the existing fixed-width candidate-quoted Q2 state.
-- There is no user-selected replacement formula and no opposite-SAT premise.
--
-- Crucial: construction of the reference graph is total, whereas fitting its
-- graph-cell budget is decidable and may return nothing. This does NOT prove
-- progress for the actual Q1 state constructor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (_<_)
open import Data.Product using (Σ)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedIndexedReferenceMachineExact as Packed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact as Graph
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1NumericIndexedGraphExact as Numeric
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedGraphCellBudgetExact as Budget

module CandidateReference
  {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (code : Actual.CandidateCodeRealization candidate)
  (codec :
    CodeQuote.FixedWidthCandidateCodeCodec
      (Actual.CandidateCodeRealization.CandidateCode code))
  where

  candidateState : Q2.BoundedSelfReferenceState
  candidateState =
    Fixed.fixedWidthCandidateQuotedState code codec

  exactCookFormula : Cook.BooleanFormula
  exactCookFormula =
    Q2.currentFormula candidateState

  exactIndexedArity : Nat
  exactIndexedArity =
    Bridge.formulaVariableBound exactCookFormula

  exactIndexedRoot :
    SAT.BooleanFormula exactIndexedArity
  exactIndexedRoot =
    Bridge.cookToIndexed exactCookFormula

  referenceGraph :
    Graph.ReferenceGraph exactIndexedArity
  referenceGraph =
    Graph.buildReferenceGraph exactIndexedArity

  referenceInitialState :
    Packed.PackedIndexedState exactIndexedArity
  referenceInitialState =
    Packed.rootPackedState exactIndexedRoot

  numericInitialState :
    Numeric.NumericState exactIndexedArity
  numericInitialState =
    Numeric.numericEncode referenceInitialState

  numericInitialStateDecodesExact :
    Numeric.numericDecode numericInitialState
    ≡
    referenceInitialState
  numericInitialStateDecodesExact =
    Numeric.numericDecodeEncode referenceInitialState

  referenceInitialStateEnumerated :
    Graph.Listed
      referenceInitialState
      (Graph.states referenceGraph)
  referenceInitialStateEnumerated =
    Graph.allPackedStatesCover
      (Fin.fromℕ exactIndexedArity)
      (Indexed.indexRestrictionNode
        (Root.rootLayerNode exactIndexedRoot))

  budgetCheckedReference :
    Maybe
      (Σ
        (Graph.ReferenceGraph exactIndexedArity)
        (λ graph →
          Budget.graphStorageCells graph
          <
          Q2.recursiveMeasure candidateState))
  budgetCheckedReference =
    Budget.budgetedReferenceGraph
      exactIndexedArity
      (Q2.recursiveMeasure candidateState)

  sameQuotedCookFormula :
    exactCookFormula
    ≡
    Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec)
  sameQuotedCookFormula =
    refl

------------------------------------------------------------------------
-- This module has NO theorem that budgetCheckedReference is just.
-- The complete Q1 compiler still needs reachability, rewrite/arity admission,
-- real interpreter work accounting, ALL-overhead strict fit, and an independent
-- noncircular first-step success proof for this very candidateState.
------------------------------------------------------------------------
