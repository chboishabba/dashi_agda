module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCoupledFirstStepBoundaryExact where

------------------------------------------------------------------------
-- CANDIDATE-COUPLED FIRST-STEP BOUNDARY
--
-- The current P lane has now paid three exact facts:
--
--   1. the raw initial-state interface is syntactically universal;
--   2. sufficiently high semantic residual width forces the direct-DP
--      constructor to return nothing;
--   3. Q1OppositeSATTerminalSemantics is already equivalent to a concrete SAT
--      decision failure and therefore cannot honestly be assumed to demand a
--      successful first step.
--
-- The remaining theorem must therefore live strictly between (1) and (3):
--
--   candidate D
--      -> candidate-dependent initial live state
--      -> a reason Q1 MUST make one successful first step there,
--
-- without already supplying a SATDecisionFailure.
--
-- This owner packages that exact boundary and proves that any such demanded
-- progress is incompatible with a width witness that already exhausts the
-- state's recursive measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; _≢_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityDirectDPObstructionExact as Equality

------------------------------------------------------------------------
-- A future genuine self-instantiation theorem must replace the current free
-- initial-state argument by a candidate-dependent root builder.
------------------------------------------------------------------------

CandidateInitialRootBuilder :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
CandidateInitialRootBuilder cost =
  Direct.PolynomialSATDeciderCandidate cost →
  Q2.BoundedSelfReferenceState

------------------------------------------------------------------------
-- "Progress" is deliberately operational and weaker than any opposite-SAT
-- semantic premise: the constructor merely must not stop at this state.
------------------------------------------------------------------------

CandidateFirstStepProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  CandidateInitialRootBuilder cost →
  DirectDP.DirectDPChargedStateConstructor →
  Direct.PolynomialSATDeciderCandidate cost →
  Set₁
CandidateFirstStepProgress
    initialFor
    constructor
    candidate =
  constructor (initialFor candidate)
  ≢
  nothing

------------------------------------------------------------------------
-- Generic high-width obstruction at a candidate-dependent initial state.
------------------------------------------------------------------------

candidateHighWidthForcesStop :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (initialFor : CandidateInitialRootBuilder cost)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (initialFor candidate))}
    remaining
    width →
  Q2.recursiveMeasure
      (initialFor candidate)
  ≤
  Width.triple width →
  constructor (initialFor candidate)
  ≡
  nothing
candidateHighWidthForcesStop
    initialFor
    constructor
    candidate
    witness
    measureBelowWidth =
  DirectDP.directDPHighWidthForcesConstructorStop
    witness
    measureBelowWidth
    constructor

candidateHighWidthRefutesDemandedProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (initialFor : CandidateInitialRootBuilder cost)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (initialFor candidate))}
    remaining
    width →
  Q2.recursiveMeasure
      (initialFor candidate)
  ≤
  Width.triple width →
  CandidateFirstStepProgress
    initialFor
    constructor
    candidate →
  ⊥
candidateHighWidthRefutesDemandedProgress
    initialFor
    constructor
    candidate
    witness
    measureBelowWidth
    mustProgress =
  mustProgress
    (candidateHighWidthForcesStop
      initialFor
      constructor
      candidate
      witness
      measureBelowWidth)

------------------------------------------------------------------------
-- Equality specialization: if the candidate-dependent root is literally the
-- existing block-equality live root and its measure is below 3*2^n, progress is
-- impossible.
------------------------------------------------------------------------

candidateBlockEqualityRefutesDemandedProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (initialFor : CandidateInitialRootBuilder cost)
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    {width : Nat} →
  Equality.BlockEqualityLiveRoot
    (initialFor candidate)
    width →
  Q2.recursiveMeasure
      (initialFor candidate)
  ≤
  Width.triple
    (DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact.bitCardinality
      width) →
  CandidateFirstStepProgress
    initialFor
    constructor
    candidate →
  ⊥
candidateBlockEqualityRefutesDemandedProgress
    initialFor
    constructor
    candidate
    realization
    measureBelowWidth
    mustProgress =
  mustProgress
    (Equality.blockEqualityHighWidthForcesDirectDPStop
      realization
      measureBelowWidth
      constructor)

------------------------------------------------------------------------
-- Candidate-local debt package.
--
-- This record intentionally does NOT include Q1OppositeSATTerminalSemantics,
-- SATDecisionFailure, or correctness of D.  It states only the missing
-- pre-failure coupling which the live programme would genuinely have to prove.
------------------------------------------------------------------------

record CandidateFirstStepCouplingDebt
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (constructor : DirectDP.DirectDPChargedStateConstructor) : Set₁ where
  constructor candidate-first-step-coupling-debt
  field
    initial :
      Q2.BoundedSelfReferenceState

    progressRequired :
      constructor initial
      ≢
      nothing

open CandidateFirstStepCouplingDebt public

highWidthRefutesCandidateFirstStepCouplingDebt :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    (debt : CandidateFirstStepCouplingDebt candidate constructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (initial debt))}
    remaining
    width →
  Q2.recursiveMeasure
      (initial debt)
  ≤
  Width.triple width →
  ⊥
highWidthRefutesCandidateFirstStepCouplingDebt
    {constructor = constructor}
    debt
    witness
    measureBelowWidth =
  progressRequired debt
    (DirectDP.directDPHighWidthForcesConstructorStop
      witness
      measureBelowWidth
      constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The P search is now max-cut:
--
--   PAID exactly:
--     width witness + resource inequality -> constructor must stop.
--
--   FORBIDDEN circular premise:
--     opposite-SAT terminal semantics, because the live branch proves that is
--     already a SAT decision failure in disguise.
--
--   ONLY RESIDUAL DEBT:
--     construct, from the candidate/self-code alone, an initial live state and
--     an operational reason the first Q1 step must succeed.
--
-- If that demanded state has width exhausting its measure, the demand is
-- impossible.  If every legitimately demanded state avoids such width, THAT
-- avoidance theorem is the special structural law of self-instantiation.
------------------------------------------------------------------------
