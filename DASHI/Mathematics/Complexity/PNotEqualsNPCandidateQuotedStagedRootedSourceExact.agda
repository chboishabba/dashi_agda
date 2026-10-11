module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedStagedRootedSourceExact where

------------------------------------------------------------------------
-- CANDIDATE-QUOTED ROOT -> TOTAL STAGED ROOTED SOURCE RESULT
--
-- This binds the new explicit source-construction stop reason to the exact
-- fixed-width same-object candidate root already present on master.
--
-- There is no free initial formula and no arbitrary budget:
--   root   = cookToIndexed(currentFormula(candidateQuotedState))
--   budget = recursiveMeasure(candidateQuotedState)
--
-- The staged result is therefore literally:
--   sourceReady ...
--   or
--   budgetExhausted on the candidate's own recursive measure.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)

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

  indexedRoot =
    Bridge.cookToIndexed
      (Q2.currentFormula candidateState)

  candidateBudget : Nat
  candidateBudget =
    Q2.recursiveMeasure candidateState

  stagedSource :
    Staged.RootedSourceStage
      indexedRoot
      candidateBudget
  stagedSource =
    Staged.stagedRootedSource
      indexedRoot
      candidateBudget

  sourceWork : Nat
  sourceWork =
    Completed.completedRootedSourceWork indexedRoot

  ----------------------------------------------------------------------
  -- Branch-local consequences expose exactly what remains to be compiled.
  ----------------------------------------------------------------------

  sourceReadyImpliesWorkFits :
    ∀ {terminalKeys exact fits} →
    stagedSource
    ≡
    Staged.sourceReady terminalKeys exact fits →
    sourceWork < candidateBudget
  sourceReadyImpliesWorkFits {fits = fits} equality =
    fits

  budgetExhaustedImpliesMeasureBelowSourceWork :
    ∀ {exhausted} →
    stagedSource
    ≡
    Staged.budgetExhausted exhausted →
    candidateBudget ≤ sourceWork
  budgetExhaustedImpliesMeasureBelowSourceWork
      {exhausted = exhausted}
      equality =
    exhausted

  ----------------------------------------------------------------------
  -- Exact root identity firewall.
  ----------------------------------------------------------------------

  candidateBudgetIsRecursiveMeasure :
    candidateBudget
    ≡
    Q2.recursiveMeasure candidateState
  candidateBudgetIsRecursiveMeasure =
    Agda.Builtin.Equality.refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- On the exact same-object candidate root, the exhaustive rooted source stage
-- is now total and its stop reason is inspectable.  If it fails, the reason is
-- precisely that its declared work exhausts the candidate state's measure.
--
-- What remains before this is a live DirectDP constructor is a compiler from
-- the successful rooted source data to the single flat TransitionTableCandidate
-- plus a literal machine trace proving that every declared source operation was
-- actually paid.
------------------------------------------------------------------------
