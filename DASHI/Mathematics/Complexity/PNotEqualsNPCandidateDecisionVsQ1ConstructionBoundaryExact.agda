module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDecisionVsQ1ConstructionBoundaryExact where

------------------------------------------------------------------------
-- CANDIDATE ROOT DECISION VS Q1 CONSTRUCTION
--
-- B0 audit of the direct-DP constructor.
--
-- DirectDPChargedStateConstructor is currently only:
--
--   state -> Maybe (DirectDPChargedConstructionRun state).
--
-- There is no implemented constructor algorithm whose failure branches can be
-- inspected. Therefore constructor state = nothing has no internal stop reason
-- in the current interface.
--
-- This owner records what a SUCCESSFUL run actually contains and separates
-- that information from the single candidate decision bit available from the
-- candidate-quoted self-application root.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed

------------------------------------------------------------------------
-- One root decision bit.
------------------------------------------------------------------------

record CandidateRootDecisionReceipt
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState) : Set where
  constructor candidate-root-decision-receipt
  field
    rootDecision : Bool

    rootDecisionExact :
      rootDecision
      ≡
      Direct.decide candidate
        (Q2.currentFormula state)

open CandidateRootDecisionReceipt public

canonicalCandidateRootDecisionReceipt :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState) →
  CandidateRootDecisionReceipt candidate state
canonicalCandidateRootDecisionReceipt candidate state =
  candidate-root-decision-receipt
    (Direct.decide candidate (Q2.currentFormula state))
    refl

------------------------------------------------------------------------
-- Candidate decisions on arbitrary restrictions.
--
-- An extensional candidate can be invoked on every restricted Cook formula.
-- This is still only a family of answer bits; it is not a quotient,
-- transition graph, semantic congruence theorem, machine trace or resource
-- receipt.
------------------------------------------------------------------------

record CandidateRestrictionDecisionOracle
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  field
    decideRestriction :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables} →
      Family.RestrictionDerivation
        (Bridge.cookToIndexed (Q2.currentFormula state))
        current →
      Bool

    decideRestrictionExact :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables}
        (derivation :
          Family.RestrictionDerivation
            (Bridge.cookToIndexed (Q2.currentFormula state))
            current) →
      decideRestriction derivation
      ≡
      Direct.decide candidate
        (Bridge.indexedToCook current)

open CandidateRestrictionDecisionOracle public

canonicalCandidateRestrictionDecisionOracle :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState) →
  CandidateRestrictionDecisionOracle candidate state
canonicalCandidateRestrictionDecisionOracle candidate state =
  record
    { decideRestriction =
        λ {current = current} derivation →
          Direct.decide candidate
            (Bridge.indexedToCook current)
    ; decideRestrictionExact =
        λ derivation → refl
    }

------------------------------------------------------------------------
-- Successful construction decomposes into four genuinely stronger surfaces.
------------------------------------------------------------------------

record DirectDPConstructionReceipt
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor direct-dp-construction-receipt
  field
    transitionTable :
      Candidate.TransitionTableCandidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    Work :
      Set

    advance :
      Work →
      DirectDP.DirectDPMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork :
      Work

    machineStepCount :
      Nat

    machineExecution :
      Executed.Iterates
        (DirectDP.directDPMachineStep advance)
        machineStepCount
        (DirectDP.working initialWork)
        (DirectDP.finished transitionTable)

    semanticAdmission :
      ArityTerminal.ArityTrackedTerminalAdmission
        transitionTable

    chargedStrict :
      (Authority.arityTerminalEvaluationCellCount
        transitionTable
        semanticAdmission
        + machineStepCount)
      +
      DirectDP.directDPAuthorityPayloadMeasure
        state
        transitionTable
        semanticAdmission
      <
      Q2.recursiveMeasure state

open DirectDPConstructionReceipt public

runToConstructionReceipt :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  DirectDP.DirectDPChargedConstructionRun state →
  DirectDPConstructionReceipt state
runToConstructionReceipt run =
  direct-dp-construction-receipt
    (DirectDP.candidate run)
    (DirectDP.Work run)
    (DirectDP.advance run)
    (DirectDP.initialWork run)
    (DirectDP.machineStepCount run)
    (DirectDP.machineExecution run)
    (DirectDP.localAdmission run)
    (DirectDP.machineEvaluationAndNextPayloadStrict run)

constructionReceiptToRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  DirectDPConstructionReceipt state →
  DirectDP.DirectDPChargedConstructionRun state
constructionReceiptToRun receipt =
  DirectDP.direct-dp-charged-construction-run
    (Work receipt)
    (advance receipt)
    (initialWork receipt)
    (transitionTable receipt)
    (machineStepCount receipt)
    (machineExecution receipt)
    (semanticAdmission receipt)
    (chargedStrict receipt)

------------------------------------------------------------------------
-- Raw transition data are cheap: every root has a one-state self-loop table.
-- Semantic admission is intentionally not manufactured.
------------------------------------------------------------------------

oneStateTransitionTable :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Candidate.TransitionTableCandidate root
oneStateTransitionTable root =
  Candidate.transition-table-candidate
    (suc zero)
    Fin.zero
    (λ state bit → Fin.zero)

------------------------------------------------------------------------
-- The current constructor interface admits an always-stop implementation.
------------------------------------------------------------------------

alwaysStopDirectDPConstructor :
  DirectDP.DirectDPChargedStateConstructor
alwaysStopDirectDPConstructor state =
  nothing

alwaysStopDirectDPConstructorExact :
  (state : Q2.BoundedSelfReferenceState) →
  alwaysStopDirectDPConstructor state
  ≡
  nothing
alwaysStopDirectDPConstructorExact state =
  refl

alwaysStopHasNoSuccessfulRun :
  (state : Q2.BoundedSelfReferenceState) →
  Σ (DirectDP.DirectDPChargedConstructionRun state)
    (λ run →
      alwaysStopDirectDPConstructor state
      ≡
      just run) →
  ⊥
alwaysStopHasNoSuccessfulRun state (run , ())

------------------------------------------------------------------------
-- Candidate self-application is compatible with immediate stop.
--
-- For the exact fixed-width candidate-quoted state, we simultaneously have a
-- concrete candidate root decision receipt and constructor = nothing. Hence
-- candidate-on-own-quote execution by itself cannot be promoted to Q1
-- construction/progress.
------------------------------------------------------------------------

candidateQuotedRootDecisionAndStop :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Σ (CandidateRootDecisionReceipt
      candidate
      (Root.fixedWidthCandidateQuotedState code codec))
    (λ receipt →
      alwaysStopDirectDPConstructor
        (Root.fixedWidthCandidateQuotedState code codec)
      ≡
      nothing)
candidateQuotedRootDecisionAndStop
    {candidate = candidate}
    code
    codec =
  canonicalCandidateRootDecisionReceipt
      candidate
      (Root.fixedWidthCandidateQuotedState code codec)
  ,
  refl

candidateQuotedRestrictionOracleAndStop :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Σ (CandidateRestrictionDecisionOracle
      candidate
      (Root.fixedWidthCandidateQuotedState code codec))
    (λ oracle →
      alwaysStopDirectDPConstructor
        (Root.fixedWidthCandidateQuotedState code codec)
      ≡
      nothing)
candidateQuotedRestrictionOracleAndStop
    {candidate = candidate}
    code
    codec =
  canonicalCandidateRestrictionDecisionOracle
      candidate
      (Root.fixedWidthCandidateQuotedState code codec)
  ,
  refl

------------------------------------------------------------------------
-- Stop opacity.
--
-- Because DirectDPChargedStateConstructor is an arbitrary Maybe-valued
-- function, there is presently no exhaustive intrinsic DirectDPStopReason to
-- recover from a nothing result. Such a theorem only becomes meaningful after
-- replacing this interface with an implemented staged constructor.
------------------------------------------------------------------------

data DirectDPStopReasonStatus : Set where
  opaqueMaybeResultOnly : DirectDPStopReasonStatus
  stagedConstructionReasonsImplemented : DirectDPStopReasonStatus

currentDirectDPStopReasonStatus :
  DirectDPStopReasonStatus
currentDirectDPStopReasonStatus =
  opaqueMaybeResultOnly

------------------------------------------------------------------------
-- B0 verdict.
--
-- Root decision information:
--     one Bool, available immediately.
--
-- Restriction decision oracle:
--     D can be queried on every restriction, but still only returns bits.
--
-- Raw transition-table shape:
--     constructible trivially, but semantically meaningless by itself.
--
-- Successful Q1/direct-DP construction additionally requires:
--     * an actual finite construction trace;
--     * arity/terminal semantic admission over all restrictions;
--     * the exact combined strict resource charge.
--
-- Therefore the next implementation target is not a proof that the current
-- arbitrary constructor must progress. It is an ACTUAL staged constructor
-- from restriction-query data, whose failures have inspectable reasons.
--
-- Once such a constructor exists, B can be recut into elimination of its
-- concrete stop reasons, and C can attack the resource/width stop branch.
------------------------------------------------------------------------
