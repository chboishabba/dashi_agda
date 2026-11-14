module DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact where

------------------------------------------------------------------------
-- ANCHORED NO-GO FOR THE FORMER LITERAL RESOURCE-CLOSING COMPILER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedStandardPolynomialCostModelExact as Cost
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as Decider
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedStandardCandidateBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact as Budget
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixSpanNecessityExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact as LiteralNoGo
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Forward

powerAtLeastOne :
  (base degree : Nat) →
  suc zero ≤ base →
  suc zero ≤ Clock.natPower base degree
powerAtLeastOne base zero basePositive = NatP.≤-refl _
powerAtLeastOne base (suc degree) basePositive =
  NatP.≤-trans
    productOneBelow
    (NatP.*-mono-≤
      basePositive
      (powerAtLeastOne base degree basePositive))
  where
    productOneBelow :
      suc zero ≤ (suc zero) * (suc zero)
    productOneBelow = NatP.≤-refl _

coefficientBelowPolynomialBudget :
  (coefficient degree size : Nat) →
  coefficient
  ≤ coefficient * Clock.natPower (suc size) degree
coefficientBelowPolynomialBudget coefficient degree size =
  NatP.≤-trans
    (NatP.≤-reflexive (sym (NatP.*-identityʳ coefficient)))
    (NatP.*-mono-≤
      (NatP.≤-refl coefficient)
      (powerAtLeastOne
        (suc size) degree (s≤s z≤n)))

zeroBudgetForcesClockCoefficientZero :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (structuralResource :
    StructuralResource.StructuralResourceClosingFixedProgramCompilation
      (LiteralNoGo.codedClockedCandidate closure candidate)) →
  Decider.clockCoefficient (LiteralNoGo.codedWitness closure candidate)
  ≡ zero
zeroBudgetForcesClockCoefficientZero closure candidate structuralResource =
  NatP.≤-antisym coefficientBelowZero z≤n
  where
    witness = LiteralNoGo.codedWitness closure candidate
    base = StructuralResource.resource structuralResource
    ownFormula = Prefix.candidateOwnFormula structuralResource
    ownSteps = Prefix.candidateOwnSteps structuralResource

    totalZero : Opposite.steps (Resource.fixed base) ≡ zero
    totalZero =
      LiteralNoGo.literalStructuralSelfQuotationForcesZeroBudget
        closure candidate structuralResource

    ownStepsZero : ownSteps ≡ zero
    ownStepsZero =
      NatP.≤-antisym ownBelowZero z≤n
      where
        ownBelowZero : ownSteps ≤ zero
        ownBelowZero
          rewrite sym totalZero =
          Budget.candidateOwnStepsFitCookBudget base

    coefficientBelowOwn :
      Decider.clockCoefficient witness ≤ ownSteps
    coefficientBelowOwn =
      coefficientBelowPolynomialBudget
        (Decider.clockCoefficient witness)
        (Decider.clockDegree witness)
        (Binary.formulaBitCodeLength ownFormula)

    coefficientBelowZero :
      Decider.clockCoefficient witness ≤ zero
    coefficientBelowZero
      rewrite sym ownStepsZero =
      coefficientBelowOwn

zeroRunFinishExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {start finish : Standard.StandardConfiguration machine} →
  Run.StandardExactRun machine zero start finish →
  finish ≡ start
zeroRunFinishExact Run.standardRunDone = refl

guardedStartStateInitial :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Standard.state (Language.guardedStandardStart input steps)
  ≡ Standard.initialState (Standard.standardControlOfConcrete machine)
guardedStartStateInitial {machine} input steps =
  Forward.concreteInitialProjectsToStandardInitial
    (Language.guardedInitialUnique input steps)
    initialEndpoint
  where
    initialEndpoint :
      Accepting.InitialInteriorRow machine (Guard.guardedInitialRow input steps)
    initialEndpoint = record
      { Accepting.interior = Guard.guardedInitialInterior input steps
      ; Accepting.headIsInitial = Guard.guardedInitialState input steps
      }

zeroCoefficientDecisionConstant :
  (closure : Cost.CodedStandardCostClosure)
  (candidate :
    Direct.PolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure))
  (coefficientZero :
    Decider.clockCoefficient (LiteralNoGo.codedWitness closure candidate)
    ≡ zero)
  (left right : Cook.BooleanFormula) →
  Direct.decide candidate left ≡ Direct.decide candidate right
zeroCoefficientDecisionConstant closure candidate coefficientZero left right =
  trans
    (sym (Candidate.decisionExact standard left))
    (trans
      (endpointConstant left)
      (trans
        (sym (endpointConstant right))
        (Candidate.decisionExact standard right)))
  where
    clocked = LiteralNoGo.codedClockedCandidate closure candidate
    standard = Clocked.standard clocked
    presentation = Candidate.presentation standard

    stepsZero :
      (formula : Cook.BooleanFormula) →
      Candidate.exactSteps standard formula ≡ zero
    stepsZero formula
      rewrite coefficientZero = refl

    finishIsStart :
      (formula : Cook.BooleanFormula) →
      Candidate.finish standard formula
      ≡ Language.guardedStandardStart
          (Candidate.encodeFormula standard formula)
          (Candidate.exactSteps standard formula)
    finishIsStart formula
      rewrite stepsZero formula =
      zeroRunFinishExact (Candidate.execution standard formula)

    finishStateInitial :
      (formula : Cook.BooleanFormula) →
      Standard.state (Candidate.finish standard formula)
      ≡ Presented.initialState presentation
    finishStateInitial formula =
      trans
        (cong Standard.state (finishIsStart formula))
        (guardedStartStateInitial
          (Candidate.encodeFormula standard formula)
          (Candidate.exactSteps standard formula))

    endpointConstant :
      (formula : Cook.BooleanFormula) →
      Local.decideEqual
        (Presented.finiteState presentation)
        (Standard.state (Candidate.finish standard formula))
        (Presented.acceptingState presentation)
      ≡
      Local.decideEqual
        (Presented.finiteState presentation)
        (Presented.initialState presentation)
        (Presented.acceptingState presentation)
    endpointConstant formula =
      cong
        (λ state →
          Local.decideEqual
            (Presented.finiteState presentation)
            state
            (Presented.acceptingState presentation))
        (finishStateInitial formula)

anchoredLiteralStructuralResourceImpossible :
  (closure : Cost.CodedStandardCostClosure)
  (anchored :
    Direct.AnchoredPolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure)) →
  StructuralResource.StructuralResourceClosingFixedProgramCompilation
    (LiteralNoGo.codedClockedCandidate closure (Direct.candidate anchored)) →
  ⊥
anchoredLiteralStructuralResourceImpossible closure anchored structuralResource =
  Direct.falseNotTrue
    (sym trueEqualsFalse)
  where
    candidate = Direct.candidate anchored
    coefficientZero =
      zeroBudgetForcesClockCoefficientZero
        closure candidate structuralResource

    anchorDecisionsEqual :
      Direct.decide candidate Cook.excludedMiddleFormula
      ≡ Direct.decide candidate Direct.contradictionFormula
    anchorDecisionsEqual =
      zeroCoefficientDecisionConstant
        closure candidate coefficientZero
        Cook.excludedMiddleFormula
        Direct.contradictionFormula

    trueEqualsFalse : true ≡ false
    trueEqualsFalse =
      trans
        (sym (Direct.acceptsKnownSatisfiable anchored))
        (trans
          anchorDecisionsEqual
          (Direct.rejectsKnownUnsatisfiable anchored))

------------------------------------------------------------------------
-- The literal B route is closed for anchored coded candidates. The surviving
-- architecture must be virtual/streaming and resource-accounted.
------------------------------------------------------------------------
