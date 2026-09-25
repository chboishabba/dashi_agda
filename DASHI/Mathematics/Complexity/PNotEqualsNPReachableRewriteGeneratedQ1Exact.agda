module DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact where

------------------------------------------------------------------------
-- REACHABLE REPRESENTATIVES REMOVE A SECOND OPAQUE SEMANTIC FIELD
--
-- Strengthens:
--   PNotEqualsNPRewriteGeneratedQ1DiscoveryExact
--
-- Rather than asking the constructor for an arbitrary Cook representative plus
-- a separate representativeEquivalent proof, each quotient state must choose
-- an ACTUAL reachable Shannon-restriction node whose generated class is that
-- state.
--
-- The representative is definitionally indexedToCook of that reachable node.
-- Its equivalence to every other node in the same state is then derived from
-- the ONE semantic congruence theorem already carried by the transition-
-- generated quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Indexed semantic equivalence -> Cook semantic equivalence.
------------------------------------------------------------------------

indexedEquivalentToCookEquivalent :
  ∀ {leftVariables rightVariables : Nat}
    {left : SAT.BooleanFormula leftVariables}
    {right : SAT.BooleanFormula rightVariables} →
  Quotient.SatisfiabilityEquivalent left right →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook left)
    (Bridge.indexedToCook right)
indexedEquivalentToCookEquivalent
    {left = left}
    {right = right}
    equivalent =
  forward , backward
  where
    forward :
      Cook.Satisfiable (Bridge.indexedToCook left) →
      Cook.Satisfiable (Bridge.indexedToCook right)
    forward leftCook =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        right
        (proj₁ equivalent
          (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
            left
            leftCook))

    backward :
      Cook.Satisfiable (Bridge.indexedToCook right) →
      Cook.Satisfiable (Bridge.indexedToCook left)
    backward rightCook =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        left
        (proj₂ equivalent
          (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
            right
            rightCook))

------------------------------------------------------------------------
-- One state representative must be an actual reachable restriction node.
------------------------------------------------------------------------

record ReachableStateRepresentative
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (generated :
      Generated.TransitionGeneratedRestrictionQuotient root)
    (state : Fin (Generated.stateCount generated)) : Set₁ where
  constructor reachable-state-representative
  field
    currentVariables : Nat
    formula : SAT.BooleanFormula currentVariables

    derivation :
      Family.RestrictionDerivation root formula

    selectsState :
      Generated.generatedSelect
        (Generated.rootState generated)
        (Generated.step generated)
        derivation
      ≡
      state

    strictlySmallerThanRoot :
      Size.formulaNodeCount
        (Bridge.indexedToCook formula)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

    rewriteProgram :
      Rewrite.RewriteProgram
        (Bridge.indexedToCook formula)

open ReachableStateRepresentative public

------------------------------------------------------------------------
-- Whole quotient with reachable representatives.
------------------------------------------------------------------------

record ReachableRewriteGeneratedClosedQuotient
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor reachable-rewrite-generated-closed-quotient
  field
    generatedQuotient :
      Generated.TransitionGeneratedRestrictionQuotient root

    stateRepresentative :
      (state : Fin (Generated.stateCount generatedQuotient)) →
      ReachableStateRepresentative generatedQuotient state

open ReachableRewriteGeneratedClosedQuotient public

representativeFormula :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : ReachableRewriteGeneratedClosedQuotient root)
    (state : Fin (Generated.stateCount (generatedQuotient closed))) →
  Cook.BooleanFormula
representativeFormula closed state =
  Bridge.indexedToCook
    (ReachableStateRepresentative.formula
      (stateRepresentative closed state))

------------------------------------------------------------------------
-- The formerly opaque representativeEquivalent proof is derived.
------------------------------------------------------------------------

derivedRepresentativeEquivalent :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed : ReachableRewriteGeneratedClosedQuotient root)
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook current)
    (representativeFormula
      closed
      (Generated.generatedSelect
        (Generated.rootState (generatedQuotient closed))
        (Generated.step (generatedQuotient closed))
        derivation))
derivedRepresentativeEquivalent closed derivation =
  indexedEquivalentToCookEquivalent
    (Generated.sameGeneratedStateImpliesSatisfiabilityEquivalent
      (generatedQuotient closed)
      derivation
      representativeDerivation
      sameGenerated)
  where
    state :
      Fin (Generated.stateCount (generatedQuotient closed))
    state =
      Generated.generatedSelect
        (Generated.rootState (generatedQuotient closed))
        (Generated.step (generatedQuotient closed))
        derivation

    source :
      ReachableStateRepresentative
        (generatedQuotient closed)
        state
    source =
      stateRepresentative closed state

    representativeDerivation :
      Family.RestrictionDerivation
        root
        (ReachableStateRepresentative.formula source)
    representativeDerivation =
      ReachableStateRepresentative.derivation source

    sameGenerated :
      Generated.generatedSelect
        (Generated.rootState (generatedQuotient closed))
        (Generated.step (generatedQuotient closed))
        derivation
      ≡
      Generated.generatedSelect
        (Generated.rootState (generatedQuotient closed))
        (Generated.step (generatedQuotient closed))
        representativeDerivation
    sameGenerated =
      sym
        (ReachableStateRepresentative.selectsState source)

------------------------------------------------------------------------
-- Compile to the rewrite-generated owner.
------------------------------------------------------------------------

toRewriteGeneratedClosedQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  ReachableRewriteGeneratedClosedQuotient root →
  RewriteGenerated.RewriteGeneratedClosedRepresentativeQuotient root
toRewriteGeneratedClosedQuotient closed =
  RewriteGenerated.rewrite-generated-closed-representative-quotient
    (generatedQuotient closed)
    (representativeFormula closed)
    (derivedRepresentativeEquivalent closed)
    (λ state →
      ReachableStateRepresentative.strictlySmallerThanRoot
        (stateRepresentative closed state))
    (λ state →
      ReachableStateRepresentative.rewriteProgram
        (stateRepresentative closed state))

------------------------------------------------------------------------
-- State-specific witness and executed constructor.
------------------------------------------------------------------------

ReachableRewriteGeneratedQ1StateWitness :
  (state : Q2.BoundedSelfReferenceState) →
  Set₁
ReachableRewriteGeneratedQ1StateWitness state =
  Σ
    (ReachableRewriteGeneratedClosedQuotient
      (Bridge.cookToIndexed
        (Q2.currentFormula state)))
    (λ closed →
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (toRewriteGeneratedClosedQuotient closed))
        (Recurrence.stateOverhead state))

toRewriteGeneratedQ1StateWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ReachableRewriteGeneratedQ1StateWitness state →
  RewriteGenerated.RewriteGeneratedQ1StateWitness state
toRewriteGeneratedQ1StateWitness
    (closed , fits) =
  toRewriteGeneratedClosedQuotient closed
  ,
  fits

record ReachableRewriteGeneratedExecutedQ1ConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor reachable-rewrite-generated-executed-q1-construction-run
  field
    MachineState : Set
    machineStep : MachineState → MachineState

    decodeReachableWitness :
      MachineState →
      Maybe (ReachableRewriteGeneratedQ1StateWitness state)

    machineStart machineFinal : MachineState
    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        machineStep
        machineStepCount
        machineStart
        machineFinal

    reachableWitness :
      ReachableRewriteGeneratedQ1StateWitness state

    machineFinalDecodesReachableWitness :
      decodeReachableWitness machineFinal
      ≡
      just reachableWitness

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (RewriteGenerated.rewriteGeneratedWitnessToLegacy
          (toRewriteGeneratedQ1StateWitness reachableWitness))
        + machineStepCount)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (RewriteGenerated.rewriteGeneratedWitnessToLegacy
            (toRewriteGeneratedQ1StateWitness reachableWitness)))
      <
      Q2.recursiveMeasure state

open ReachableRewriteGeneratedExecutedQ1ConstructionRun public

mapReachableWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  Maybe (ReachableRewriteGeneratedQ1StateWitness state) →
  Maybe (RewriteGenerated.RewriteGeneratedQ1StateWitness state)
mapReachableWitness nothing =
  nothing
mapReachableWitness (just witness) =
  just (toRewriteGeneratedQ1StateWitness witness)

reachableRunToRewriteGeneratedRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ReachableRewriteGeneratedExecutedQ1ConstructionRun state →
  RewriteGenerated.RewriteGeneratedExecutedQ1ConstructionRun state
reachableRunToRewriteGeneratedRun {state} run =
  RewriteGenerated.rewrite-generated-executed-q1-construction-run
    (MachineState run)
    (machineStep run)
    (λ machineState →
      mapReachableWitness
        (decodeReachableWitness run machineState))
    (machineStart run)
    (machineFinal run)
    (machineStepCount run)
    (machineExecution run)
    (toRewriteGeneratedQ1StateWitness
      (reachableWitness run))
    finalDecodes
    (machineConstructionAndNextStrict run)
  where
    finalDecodes :
      mapReachableWitness
        (decodeReachableWitness run (machineFinal run))
      ≡
      just
        (toRewriteGeneratedQ1StateWitness
          (reachableWitness run))
    finalDecodes
      rewrite
        machineFinalDecodesReachableWitness run =
      refl

ReachableRewriteGeneratedExecutedQ1StateConstructor : Set₁
ReachableRewriteGeneratedExecutedQ1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (ReachableRewriteGeneratedExecutedQ1ConstructionRun state)

reachableConstructorToRewriteGenerated :
  ReachableRewriteGeneratedExecutedQ1StateConstructor →
  RewriteGenerated.RewriteGeneratedExecutedQ1StateConstructor
reachableConstructorToRewriteGenerated constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (reachableRunToRewriteGeneratedRun run)

reachableConstructorToQ2StepSystem :
  ReachableRewriteGeneratedExecutedQ1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
reachableConstructorToQ2StepSystem constructor =
  RewriteGenerated.rewriteGeneratedConstructorToQ2StepSystem
    (reachableConstructorToRewriteGenerated constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Removed from the preferred constructor:
--   * arbitrary classifier;
--   * arbitrary structural representative chain;
--   * arbitrary representativeEquivalent proof.
--
-- Remaining semantic theorem:
--   generated-state congruence.
--
-- Remaining construction data:
--   * stateCount/rootState/step;
--   * one actually reachable representative node per state;
--   * strict-size proof for each representative;
--   * evaluator-verified rewrite program from each representative to a literal
--     constant.
--
-- This is a materially smaller and more intensional Q1 target.
------------------------------------------------------------------------
