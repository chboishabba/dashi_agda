module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateRestrictionQueryCostExact where

------------------------------------------------------------------------
-- CANDIDATE RESTRICTION QUERY COST
--
-- Candidate self-application supplies one root decision bit.  A Q1/direct-DP
-- construction needs enough finite state to represent residual behavior across
-- restrictions.
--
-- This owner formalizes the simplest charged candidate-query route:
--
--   one candidate invocation per represented Q1 state.
--
-- It does NOT assert that every construction must use that strategy.  Instead
-- it proves the exact consequence:
--
--   residual width <= stateCount <= candidateQueryCount.
--
-- Therefore on a width-w layer, any such construction needs at least w
-- candidate invocations.  For block equality this is 2^n.
--
-- Any sub-width candidate-specific construction must therefore exploit genuine
-- sharing/compression beyond one-query-per-distinct-state enumeration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityDirectDPObstructionExact as Equality
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits

------------------------------------------------------------------------
-- Candidate-query accounting attached to one successful direct-DP run.
------------------------------------------------------------------------

record CandidateRestrictionQueryConstruction
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidateDecider : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor candidate-restriction-query-construction
  field
    run :
      DirectDP.DirectDPChargedConstructionRun state

    candidateQueryCount :
      Nat

    oneQueryPerRepresentedState :
      Candidate.stateCount
        (DirectDP.candidate run)
      ≤
      candidateQueryCount

    candidateQueriesChargedToMachineSteps :
      candidateQueryCount
      ≤
      DirectDP.machineStepCount run

open CandidateRestrictionQueryConstruction public

------------------------------------------------------------------------
-- Width reappears as query count.
------------------------------------------------------------------------

residualWidthBelowCandidateQueryCount :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidateDecider : Direct.PolynomialSATDeciderCandidate cost}
    {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (construction :
      CandidateRestrictionQueryConstruction
        candidateDecider
        state) →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  width
  ≤
  candidateQueryCount construction
residualWidthBelowCandidateQueryCount construction witness =
  NatP.≤-trans
    (DirectDP.directDPResidualWidthBelowStateCount
      (run construction)
      witness)
    (oneQueryPerRepresentedState construction)

residualWidthBelowMachineStepCount :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidateDecider : Direct.PolynomialSATDeciderCandidate cost}
    {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (construction :
      CandidateRestrictionQueryConstruction
        candidateDecider
        state) →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  width
  ≤
  DirectDP.machineStepCount
    (run construction)
residualWidthBelowMachineStepCount construction witness =
  NatP.≤-trans
    (NatP.≤-trans
      (DirectDP.directDPResidualWidthBelowStateCount
        (run construction)
        witness)
      (oneQueryPerRepresentedState construction))
    (candidateQueriesChargedToMachineSteps construction)

------------------------------------------------------------------------
-- Block-equality stress case.
------------------------------------------------------------------------

blockEqualityNeedsExponentialCandidateQueries :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidateDecider : Direct.PolynomialSATDeciderCandidate cost}
    {state : Q2.BoundedSelfReferenceState}
    {width : Nat} →
  Equality.BlockEqualityLiveRoot state width →
  (construction :
    CandidateRestrictionQueryConstruction
      candidateDecider
      state) →
  Bits.bitCardinality width
  ≤
  candidateQueryCount construction
blockEqualityNeedsExponentialCandidateQueries
    realization
    construction =
  residualWidthBelowCandidateQueryCount
    construction
    (Equality.liveBlockEqualityResidualWidth
      realization)

blockEqualityNeedsExponentialMachineSteps :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidateDecider : Direct.PolynomialSATDeciderCandidate cost}
    {state : Q2.BoundedSelfReferenceState}
    {width : Nat} →
  Equality.BlockEqualityLiveRoot state width →
  (construction :
    CandidateRestrictionQueryConstruction
      candidateDecider
      state) →
  Bits.bitCardinality width
  ≤
  DirectDP.machineStepCount
    (run construction)
blockEqualityNeedsExponentialMachineSteps
    realization
    construction =
  residualWidthBelowMachineStepCount
    construction
    (Equality.liveBlockEqualityResidualWidth
      realization)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Candidate execution on restrictions is not itself a compression mechanism.
--
-- If Q1 is built by paying at least one candidate call for every represented
-- state, then semantic width lower-bounds both query count and machine steps.
--
-- Thus for block equality:
--
--   2^n <= candidate queries <= charged machine steps.
--
-- This does not rule out a more clever candidate-specific construction.  It
-- identifies exactly what such a construction must provide: a way to share or
-- infer many semantically distinct restriction states without one charged
-- candidate invocation per represented state.
--
-- THAT sharing theorem, not root self-application, is the missing B1
-- mechanism.
------------------------------------------------------------------------
