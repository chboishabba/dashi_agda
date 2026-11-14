module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCandidateCodeRealizationExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED TM -> LEGACY CANDIDATE CODE REALIZATION
--
-- The legacy semantic-quotation stack asks for an abstract CandidateCode carrier.
-- We now have a stronger object: a literal CodedFiniteStandardTM together with
-- an actual quiescent execution whose final control equals the candidate decision.
--
-- Rather than inventing a universal interpreter, bind the legacy carrier to the
-- singleton SAME-CODE fibre over that actual machine.  Every inhabitant includes
-- proof that its code is literally the witness code.  The designated code's
-- Boolean output is read from the actual halting state.
--
-- This pays candidate-code identity honestly.  It does NOT provide execution for
-- arbitrary unrelated codes and does NOT solve the remaining self-specializer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- 1. Singleton same-code carrier.
------------------------------------------------------------------------

record SameCandidateCode
    {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider) : Set where
  constructor same-candidate-code
  field
    suppliedCode : Coded.CodedFiniteStandardTM
    suppliedCodeExact : suppliedCode ≡ Halting.code witness

open SameCandidateCode public

sameCandidateCodeProjectionExact :
  ∀ {decider : Cook.BooleanFormula → Bool}
    {witness : Halting.CodedStandardHaltingPolynomialDecider decider}
    (bound : SameCandidateCode witness) →
  suppliedCode bound ≡ Halting.code witness
sameCandidateCodeProjectionExact = suppliedCodeExact

literalSameCandidateCode :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider) →
  SameCandidateCode witness
literalSameCandidateCode witness =
  same-candidate-code (Halting.code witness) refl

------------------------------------------------------------------------
-- 2. Output is the actual final-control decision of the witness execution.
------------------------------------------------------------------------

actualFinishDecision :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider) →
  Cook.BooleanFormula → Bool
actualFinishDecision witness formula =
  Coded.finEqual
    (Standard.state (Halting.finish witness formula))
    (Coded.acceptingState (Halting.code witness))

haltingCandidateCodeDecisionFromActualFinish :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Halting.CodedStandardHaltingPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  actualFinishDecision witness formula ≡ decider formula
haltingCandidateCodeDecisionFromActualFinish = Halting.decisionExact

------------------------------------------------------------------------
-- 3. Legacy CandidateCodeRealization is now inhabited from the actual code/run.
------------------------------------------------------------------------

haltingCandidateCodeRealization :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Actual.CandidateCodeRealization candidate
haltingCandidateCodeRealization {candidate = candidate} witness = record
  { Actual.CandidateCode = SameCandidateCode witness
  ; Actual.candidateCode = literalSameCandidateCode witness
  ; Actual.runCandidateCode = λ supplied formula →
      actualFinishDecision witness formula
  ; Actual.codeDecisionExact =
      Halting.decisionExact witness
  }

haltingCandidateCodeIsLiteralCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  suppliedCode
    (Actual.CandidateCodeRealization.candidateCode
      (haltingCandidateCodeRealization witness))
  ≡ Halting.code witness
haltingCandidateCodeIsLiteralCode witness = refl

------------------------------------------------------------------------
-- 4. Attribution / max-cut boundary.
------------------------------------------------------------------------

record HaltingCandidateCodeBoundary : Set where
  constructor halting-candidate-code-boundary
  field
    literalCodedMachineBound : Bool
    actualHaltingDecisionUsed : Bool
    everyCarrierInhabitantProvesSameCode : Bool
    arbitraryCodeInterpreterClaimed : Bool
    oldCodeSocketPaid : Bool
    behaviouralSelfSpecializerStillRequired : Bool

canonicalHaltingCandidateCodeBoundary : HaltingCandidateCodeBoundary
canonicalHaltingCandidateCodeBoundary =
  halting-candidate-code-boundary
    true true true false true true

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The old CandidateCodeRealization socket is no longer an honest frontier item.
-- It can be inhabited from each actual-halting coded candidate while preserving
-- literal code identity and reading the decision from that machine's real final
-- control.  The remaining theorem is not candidate-code binding; it is the
-- construction of a self-specializing opposite target whose quoted-code operand
-- genuinely controls the generated own-Cook behaviour.
------------------------------------------------------------------------
