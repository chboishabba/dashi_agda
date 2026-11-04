module DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeEndpointDecisionExact where

------------------------------------------------------------------------
-- ONE ENDPOINT DECISION EQUALITY PAYS FIXED OPPOSITE SEMANTICS
--
-- FixedConcreteTapeSemanticQuotationExact asks for two implications connecting
-- the abstract fixed opposite run to the concrete accepting endpoint.
--
-- For a deterministic final row those implications are equivalent to one
-- stronger same-object equality:
--
--   endpointDecision(final)
--     = not (candidate decides own guarded Cook formula).
--
-- The generic final-state equality/acceptance lemmas then derive both semantic
-- directions automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedConcreteTapeSemanticQuotationExact as Concrete
import DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicConcreteTapeExecutionExact as Deterministic
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard

justInjective :
  ∀ {left right : Bool} →
  just left ≡ just right →
  left ≡ right
justInjective refl = refl

------------------------------------------------------------------------
-- Stronger fixed opposite machine receipt.
------------------------------------------------------------------------

record FixedOppositeEndpointDecisionRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    concrete :
      Concrete.FixedConcreteOppositeMachine code

    successor :
      Deterministic.DeterministicTapeSuccessor
        (Concrete.machine concrete)

    successorComplete :
      Deterministic.DeterministicRefinementComplete
        (Concrete.machine concrete)
        successor

    finish :
      Local.TapeRow (Concrete.machine concrete)

    execution :
      Deterministic.DeterministicExecution
        successor
        (Concrete.steps concrete)
        (Guard.guardedInitialRow
          (Concrete.input concrete)
          (Concrete.steps concrete))
        finish

    initialEndpoint :
      Accepting.InitialInteriorRow
        (Concrete.machine concrete)
        (Guard.guardedInitialRow
          (Concrete.input concrete)
          (Concrete.steps concrete))

    finalInterior :
      Locality.InteriorHeadConfiguration
        (Concrete.machine concrete)
        finish

    endpointDecisionExact :
      Tape.endpointDecision finalInterior
      ≡
      Opposite.notBool
        (Direct.decide
          candidate
          (Concrete.fixedCookFormula concrete))

open FixedOppositeEndpointDecisionRealization public

------------------------------------------------------------------------
-- Derive the older two-direction fixed concrete realization.
------------------------------------------------------------------------

endpointDecisionToFixedConcreteRealization :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedOppositeEndpointDecisionRealization code →
  Concrete.FixedConcreteOppositeRealization code
endpointDecisionToFixedConcreteRealization
    {candidate = candidate}
    realization = record
  { Concrete.concrete = concrete realization
  ; Concrete.successor = successor realization
  ; Concrete.successorComplete = successorComplete realization
  ; Concrete.finish = finish realization
  ; Concrete.execution = execution realization
  ; Concrete.initialEndpoint = initialEndpoint realization
  ; Concrete.fixedRunTrueGivesAcceptingEndpoint =
      fixedRunTrueGivesAccepting
  ; Concrete.acceptingEndpointGivesFixedRunTrue =
      acceptingGivesFixedRunTrue
  }
  where
    ownFormula : Cook.BooleanFormula
    ownFormula =
      Concrete.fixedCookFormula (concrete realization)

    oppositeBit : Bool
    oppositeBit =
      Opposite.notBool (Direct.decide candidate ownFormula)

    fixedRunExactLocal :
      Fixed.fixedRun code ownFormula
      ≡ just oppositeBit
    fixedRunExactLocal =
      Fixed.fixedRunExact code ownFormula

    fixedRunTrueGivesAccepting :
      Fixed.fixedRun code ownFormula ≡ just true →
      Accepting.AcceptingInteriorRow
        (Concrete.machine (concrete realization))
        (finish realization)
    fixedRunTrueGivesAccepting returnedTrue =
      Tape.endpointDecisionTrueGivesAccepting
        (finalInterior realization)
        endpointTrue
      where
        oppositeTrue : oppositeBit ≡ true
        oppositeTrue =
          justInjective
            (trans
              (sym fixedRunExactLocal)
              returnedTrue)

        endpointTrue :
          Tape.endpointDecision (finalInterior realization)
          ≡ true
        endpointTrue =
          trans
            (endpointDecisionExact realization)
            oppositeTrue

    acceptingGivesFixedRunTrue :
      Accepting.AcceptingInteriorRow
        (Concrete.machine (concrete realization))
        (finish realization) →
      Fixed.fixedRun code ownFormula ≡ just true
    acceptingGivesFixedRunTrue accepting =
      trans
        fixedRunExactLocal
        (cong just oppositeTrue)
      where
        endpointTrue :
          Tape.endpointDecision (finalInterior realization)
          ≡ true
        endpointTrue =
          Tape.acceptingGivesEndpointDecisionTrue accepting

        oppositeTrue : oppositeBit ≡ true
        oppositeTrue =
          trans
            (sym (endpointDecisionExact realization))
            endpointTrue

------------------------------------------------------------------------
-- Decision failure and universal producer at the reduced interface.
------------------------------------------------------------------------

endpointDecisionRealizationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FixedOppositeEndpointDecisionRealization code →
  Direct.SATDecisionFailure candidate
endpointDecisionRealizationGivesDecisionFailure code realization =
  Concrete.fixedConcreteRealizationGivesDecisionFailure
    code
    (endpointDecisionToFixedConcreteRealization realization)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The diagonal constructor no longer owes two independent semantic directions.
-- It owes one deterministic same-object equation:
--
--   final accepting-control bit
--     = not D(guardedCookFormula of this exact machine/input/clock).
--
-- Together with local step soundness/completeness and an exact deterministic
-- execution trace, every Cook--Levin semantic implication is inherited.
------------------------------------------------------------------------
