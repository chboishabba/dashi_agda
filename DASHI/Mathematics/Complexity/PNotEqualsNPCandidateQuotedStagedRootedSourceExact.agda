module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedStagedRootedSourceExact where

------------------------------------------------------------------------
-- EXACT CANDIDATE-QUOTED ROOT -> TOTAL ROOTED SOURCE STAGE
--
-- Same-object weld:
--   executable candidate-code realization
--   + fixed-width codec
--   -> exact candidate-quoted Q2 state s_D
--   -> exact indexed root currentFormula(s_D)
--   -> total staged rooted-source outcome at recursiveMeasure(s_D).
--
-- This does not assume SAT correctness, opposite-SAT semantics or mandatory
-- Q1 progress.  It makes the first exhaustive-constructor branch explicit on
-- the exact candidate-coupled state.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact as Completed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1StagedRootedConstructorExact as Staged

module CandidateStage
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

  indexedArity : Nat
  indexedArity =
    Bridge.formulaVariableBound
      (Q2.currentFormula candidateState)

  indexedRoot :
    DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact.BooleanFormula
      indexedArity
  indexedRoot =
    Bridge.cookToIndexed
      (Q2.currentFormula candidateState)

  candidateBudget : Nat
  candidateBudget =
    Q2.recursiveMeasure candidateState

  rootedSourceOutcome :
    Staged.RootedSourceStageResult
      indexedRoot
      candidateBudget
  rootedSourceOutcome =
    Staged.runRootedSourceStage
      indexedRoot
      candidateBudget

  ----------------------------------------------------------------------
  -- The exact exhaustive-constructor source-work obstruction.
  ----------------------------------------------------------------------

  sourceWorkExhaustion : Set
  sourceWorkExhaustion =
    candidateBudget
    ≤
    Completed.completedRootedSourceWork indexedRoot

  sourceWorkFits : Set
  sourceWorkFits =
    Completed.completedRootedSourceWork indexedRoot
    <
    candidateBudget

  sourceExhaustionForcesStageFailure :
    sourceWorkExhaustion →
    Completed.completedRootedSourceGate
      indexedRoot
      candidateBudget
    ≡
    Data.Maybe.Base.nothing
  sourceExhaustionForcesStageFailure =
    Staged.sourceExhaustionImpliesCompletedGateFailure

  sourceReadyExcludesExhaustion :
    Staged.RootedSourceReady indexedRoot candidateBudget →
    sourceWorkExhaustion →
    ⊥
  sourceReadyExcludesExhaustion ready exhausted =
    Data.Nat.Properties.<⇒≱
      (Staged.sourceWorkFits ready)
      exhausted

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- On the exact candidate-coupled state, the exhaustive source constructor is
-- no longer an abstract possibility. Its first stage has a total computed
-- outcome.  If source work exhausts the recursive measure, this construction
-- route is closed. If sourceReady is returned, the remaining debts are the
-- explicitly staged global packing/admission/emitting-machine/full-charge
-- obligations.
--
-- A theorem that every polynomial candidate MUST nevertheless progress cannot
-- be obtained from this source gate: it must either prove strict source fit on
-- the candidate-generated root or provide a cheaper non-exhaustive constructor.
------------------------------------------------------------------------
