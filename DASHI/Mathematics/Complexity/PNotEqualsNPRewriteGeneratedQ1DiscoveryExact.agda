module DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact where

------------------------------------------------------------------------
-- GENERATED Q1 DISCOVERY WITH EXECUTABLE STRUCTURAL REWRITE PROGRAMS
--
-- Strengthens:
--   PNotEqualsNPGeneratedClosedQ1DiscoveryExact
--
-- by replacing each opaque StructuralRepresentativeChain with a restricted
-- RewriteProgram from:
--   PNotEqualsNPAnswerBlindStructuralRewriteMachineExact.
--
-- The compiler reconstructs the legacy chain automatically.  Thus the Q1
-- discovery payload no longer receives arbitrary equisatisfiability proofs for
-- representative descent.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPGeneratedClosedQ1DiscoveryExact as Legacy
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Executable rewrite-machine configurations.
------------------------------------------------------------------------

RewriteConfiguration : Set₁
RewriteConfiguration =
  Σ Cook.BooleanFormula Rewrite.RewriteProgram

rewriteStep :
  RewriteConfiguration →
  RewriteConfiguration
rewriteStep (formula , Rewrite.halt value) =
  formula , Rewrite.halt value
rewriteStep
    (formula , Rewrite.step {after = after} rewrite rest) =
  after , rest

rewriteProgramStepCount :
  ∀ {formula} →
  Rewrite.RewriteProgram formula →
  Nat
rewriteProgramStepCount (Rewrite.halt value) =
  zero
rewriteProgramStepCount (Rewrite.step rewrite rest) =
  suc (rewriteProgramStepCount rest)

rewriteProgramTrace :
  ∀ {formula} →
  Rewrite.RewriteProgram formula →
  List RewriteConfiguration
rewriteProgramTrace {formula} (Rewrite.halt value) =
  (formula , Rewrite.halt value) ∷ []
rewriteProgramTrace {formula}
    (Rewrite.step {after = after} rewrite rest) =
  (formula , Rewrite.step rewrite rest)
  ∷
  rewriteProgramTrace rest

rewriteProgramPath :
  ∀ {formula} →
  Rewrite.RewriteProgram formula →
  Complexity.ExecutionFibrePath RewriteConfiguration
rewriteProgramPath program =
  Complexity.executionFibrePath
    (rewriteProgramTrace program)

rewriteProgramTransitionCostExact :
  ∀ {formula}
    (program : Rewrite.RewriteProgram formula) →
  Complexity.K
    Complexity.transitionConsumer
    (rewriteProgramPath program)
  ≡
  rewriteProgramStepCount program
rewriteProgramTransitionCostExact (Rewrite.halt value) =
  refl
rewriteProgramTransitionCostExact
    (Rewrite.step rewrite rest)
    rewrite rewriteProgramTransitionCostExact rest =
  refl

------------------------------------------------------------------------
-- Rewrite-backed generated quotient.
------------------------------------------------------------------------

record RewriteGeneratedClosedRepresentativeQuotient
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor rewrite-generated-closed-representative-quotient
  field
    generatedQuotient :
      Generated.TransitionGeneratedRestrictionQuotient root

    representative :
      Fin (Generated.stateCount generatedQuotient) →
      Cook.BooleanFormula

    representativeEquivalent :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables}
        (derivation :
          Family.RestrictionDerivation root current) →
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (representative
          (Generated.generatedSelect
            (Generated.rootState generatedQuotient)
            (Generated.step generatedQuotient)
            derivation))

    representativeStrictlySmallerThanRoot :
      (state : Fin (Generated.stateCount generatedQuotient)) →
      Size.formulaNodeCount
        (representative state)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

    representativeRewriteProgram :
      (state : Fin (Generated.stateCount generatedQuotient)) →
      Rewrite.RewriteProgram
        (representative state)

open RewriteGeneratedClosedRepresentativeQuotient public

------------------------------------------------------------------------
-- Compile rewrite programs to the legacy generated closed payload.
------------------------------------------------------------------------

toGeneratedClosedRepresentativeQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  RewriteGeneratedClosedRepresentativeQuotient root →
  Legacy.GeneratedClosedRepresentativeQuotient root
toGeneratedClosedRepresentativeQuotient rewriteClosed =
  Legacy.generated-closed-representative-quotient
    (generatedQuotient rewriteClosed)
    (representative rewriteClosed)
    (representativeEquivalent rewriteClosed)
    (representativeStrictlySmallerThanRoot rewriteClosed)
    (λ state →
      Rewrite.compileRewriteProgram
        (representativeRewriteProgram rewriteClosed state))

toClosedStrictRepresentativeQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  RewriteGeneratedClosedRepresentativeQuotient root →
  Closed.ClosedStrictRepresentativeQuotient root
toClosedStrictRepresentativeQuotient rewriteClosed =
  Legacy.toClosedStrictRepresentativeQuotient
    (toGeneratedClosedRepresentativeQuotient rewriteClosed)

------------------------------------------------------------------------
-- State-specific rewrite-backed Q1 witness.
------------------------------------------------------------------------

RewriteGeneratedQ1StateWitness :
  (state : Q2.BoundedSelfReferenceState) →
  Set₁
RewriteGeneratedQ1StateWitness state =
  Σ
    (RewriteGeneratedClosedRepresentativeQuotient
      (Bridge.cookToIndexed
        (Q2.currentFormula state)))
    (λ rewriteClosed →
      Q1.ClosedQuotientAllOverheadFits
        (toClosedStrictRepresentativeQuotient rewriteClosed)
        (Recurrence.stateOverhead state))

rewriteGeneratedWitnessToLegacy :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  RewriteGeneratedQ1StateWitness state →
  Recurrence.Q1StateWitness state
rewriteGeneratedWitnessToLegacy
    (rewriteClosed , fits) =
  toClosedStrictRepresentativeQuotient rewriteClosed
  ,
  fits

------------------------------------------------------------------------
-- Preferred construction-machine payload.
------------------------------------------------------------------------

record RewriteGeneratedExecutedQ1ConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor rewrite-generated-executed-q1-construction-run
  field
    MachineState : Set
    machineStep : MachineState → MachineState

    decodeRewriteGeneratedWitness :
      MachineState →
      Maybe (RewriteGeneratedQ1StateWitness state)

    machineStart machineFinal : MachineState
    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        machineStep
        machineStepCount
        machineStart
        machineFinal

    rewriteGeneratedWitness :
      RewriteGeneratedQ1StateWitness state

    machineFinalDecodesRewriteGeneratedWitness :
      decodeRewriteGeneratedWitness machineFinal
      ≡
      just rewriteGeneratedWitness

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (rewriteGeneratedWitnessToLegacy rewriteGeneratedWitness)
        + machineStepCount)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (rewriteGeneratedWitnessToLegacy rewriteGeneratedWitness))
      <
      Q2.recursiveMeasure state

open RewriteGeneratedExecutedQ1ConstructionRun public

mapRewriteGeneratedWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  Maybe (RewriteGeneratedQ1StateWitness state) →
  Maybe (Recurrence.Q1StateWitness state)
mapRewriteGeneratedWitness nothing =
  nothing
mapRewriteGeneratedWitness (just witness) =
  just (rewriteGeneratedWitnessToLegacy witness)

rewriteGeneratedRunToExecutedRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  RewriteGeneratedExecutedQ1ConstructionRun state →
  Executed.ExecutedQ1ConstructionRun state
rewriteGeneratedRunToExecutedRun {state} run =
  Executed.executed-q1-construction-run
    (MachineState run)
    (machineStep run)
    (λ machineState →
      mapRewriteGeneratedWitness
        (decodeRewriteGeneratedWitness run machineState))
    (machineStart run)
    (machineFinal run)
    (machineStepCount run)
    (machineExecution run)
    (rewriteGeneratedWitnessToLegacy
      (rewriteGeneratedWitness run))
    finalDecodesLegacy
    (machineConstructionAndNextStrict run)
  where
    finalDecodesLegacy :
      mapRewriteGeneratedWitness
        (decodeRewriteGeneratedWitness run (machineFinal run))
      ≡
      just
        (rewriteGeneratedWitnessToLegacy
          (rewriteGeneratedWitness run))
    finalDecodesLegacy
      rewrite
        machineFinalDecodesRewriteGeneratedWitness run =
      refl

RewriteGeneratedExecutedQ1StateConstructor : Set₁
RewriteGeneratedExecutedQ1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (RewriteGeneratedExecutedQ1ConstructionRun state)

rewriteGeneratedConstructorToExecuted :
  RewriteGeneratedExecutedQ1StateConstructor →
  Executed.ExecutedQ1StateConstructor
rewriteGeneratedConstructorToExecuted constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (rewriteGeneratedRunToExecutedRun run)

rewriteGeneratedConstructorToQ2StepSystem :
  RewriteGeneratedExecutedQ1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
rewriteGeneratedConstructorToQ2StepSystem constructor =
  Executed.executedConstructorToQ2StepSystem
    (rewriteGeneratedConstructorToExecuted constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The opaque representative-chain constructor is now off the preferred path.
--
-- The remaining discovery object for each quotient state is:
--
--   representative formula
--   + a program in the fixed structural rewrite language reducing it to a
--     literal constant.
--
-- The rewrite program cannot import an arbitrary equisatisfiability witness;
-- the compiler derives every semantic step from evaluator-verified rewrite
-- constructors.
--
-- Remaining hard obligations:
--   * generated-state semantic congruence;
--   * strict representative discovery;
--   * show those representatives normalize under this rewrite language
--     (or identify the next sound structural opcode);
--   * implement the outer constructor as a restricted audited machine rather
--     than a client-supplied arbitrary step/decoder.
------------------------------------------------------------------------
