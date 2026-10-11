module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedStagedRootedSourceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact as Completed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1StagedRootedSourceConstructorExact as Staged

module CandidateStagedSource
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

  indexedRoot :
    SAT.BooleanFormula
      (Bridge.formulaVariableBound
        (Q2.currentFormula candidateState))
  indexedRoot =
    Bridge.cookToIndexed
      (Q2.currentFormula candidateState)

  candidateBudget : Nat
  candidateBudget =
    Q2.recursiveMeasure candidateState

  stagedSource :
    Staged.RootedSourceStage indexedRoot candidateBudget
  stagedSource =
    Staged.stagedRootedSource indexedRoot candidateBudget

  sourceWork : Nat
  sourceWork =
    Completed.completedRootedSourceWork indexedRoot

  sourceReadyImpliesWorkFits :
    ∀ {terminalKeys exact fits} →
    stagedSource
    ≡ Staged.sourceReady terminalKeys exact fits →
    sourceWork < candidateBudget
  sourceReadyImpliesWorkFits {fits = fits} equality = fits

  budgetExhaustedImpliesMeasureBelowSourceWork :
    ∀ {exhausted} →
    stagedSource
    ≡ Staged.budgetExhausted exhausted →
    candidateBudget ≤ sourceWork
  budgetExhaustedImpliesMeasureBelowSourceWork
      {exhausted = exhausted}
      equality = exhausted

  candidateBudgetIsRecursiveMeasure :
    candidateBudget ≡ Q2.recursiveMeasure candidateState
  candidateBudgetIsRecursiveMeasure = refl
