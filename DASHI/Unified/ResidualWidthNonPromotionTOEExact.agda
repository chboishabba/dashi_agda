module DASHI.Unified.ResidualWidthNonPromotionTOEExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Connect the exact residual-width derivations, resource obstructions, and
-- non-promotion theorems to the focused DASHI TOE graph.
--
-- R. Reuse.
-- Reuse the literal block-equality residual-width witness.
-- Reuse the same-formula linear decision separation theorem.
-- Reuse the conditional direct-DP width obstruction.
-- Reuse the generic self-specialization width-universality no-go theorem.
-- Reuse the candidate-first-step coupling boundary.
-- Reuse the exhaustive rooted-builder budget failure theorem.
-- Reuse the candidate future-transport no-go theorem.
-- Reuse the stuttering decision-preservation theorem.
-- Reuse the finite-interpreter linear work bound.
-- Reuse the same-machine finite-program/Cook--Levin weld.
--
-- C. Construction.
-- Expose theorem-bearing aliases only.
-- Add no new residual-width theorem.
-- Add no new SAT lower-bound theorem.
-- Add no new Q1 authority.
--
-- S. Safety invariants.
-- Ordered residual width is not arbitrary deterministic decision time.
-- A block-equality direct-DP obstruction requires the same-object live root.
-- Generic self-specialization does not force small Shannon width.
-- High width only refutes a first step when that first step is independently
-- required on the same candidate-derived state.
-- Failure of one exhaustive Q1 builder is not failure of every SAT algorithm.
-- Present Boolean output is not a future-safe quotient of machine state.
-- Stuttering is a semantics-preserving representation change.
-- Interpreter work remains explicitly charged.
-- Finite program serialization and Cook--Levin reduction stay on one machine.
--
-- L. Lane.
-- This module owns only complexity non-promotion normalization.
-- It does not edit ESD or digital_esd modules.
-- It does not copy code from casey-git-clone, zkSEC, or meta-introspector.
--
-- P. Postconditions.
-- TOE consumers reach one normalized exact surface for residual width,
-- conditional direct-DP obstruction, non-promotion, machine preservation,
-- interpreter work, and the same-machine Cook--Levin weld.
--
-- G. Governance.
-- Original theorem owners retain proof ownership.
-- Existing source modules remain the mathematical authorities.
-- The meta-introspector zkperf, zos-server, erdfa-py, and aristotle-cli-rs
-- repositories remain attributed tooling/process donors only.
-- No theorem body or source code is copied from them here.
--
-- F. Verification.
-- The regression module checks that Unifier re-exports these exact owners.
-- Source read-back checks every import and trust-escape boundary.
-- Kernel certification still requires an exact-head Agda or CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (Maybe; nothing)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalCandidateAbstractMachineExact as CandidateMachine
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact as EqualityWidth
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityLinearDecisionSeparationExact as EqualityDecision
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityDirectDPObstructionExact as EqualityDirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExhaustiveEnumerationCostObstructionExact as Exhaustive
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateConfigurationFutureTransportNoGoExact as Future
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfSpecializationWidthUniversalityNoGoExact as SelfSpecialization
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCoupledFirstStepBoundaryExact as FirstStep
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.DeterministicMachineToInPExact as ToP
import DASHI.Mathematics.Complexity.PNotEqualsNPActualMachineStutteringTransportExact as Stutter
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTapeStutteringCalibrationExact as Tape
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCookLevinSameObjectWeldExact as Weld

------------------------------------------------------------------------
-- Exact source theorems, normalized for TOE consumers.
------------------------------------------------------------------------

toeBlockEqualityResidualWidthWitness :
  (width : Nat) →
  Width.ResidualWidthWitness
    {root = EqualityWidth.blockEqualityFormula width}
    width
    (Bits.bitCardinality width)
toeBlockEqualityResidualWidthWitness =
  EqualityWidth.blockEqualityResidualWidthWitness

toeSameFormulaDecisionExact :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₁ (EqualityDecision.equalityDecisionWithCount left right)
  ≡
  SAT.evaluate
    (EqualityWidth.blockEqualityFormula width)
    (EqualityWidth.blockAssignment left right)
toeSameFormulaDecisionExact =
  EqualityDecision.linearDecisionAgreesWithBlockEqualityFormula

toeDecisionCountExact :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₂ (EqualityDecision.equalityDecisionWithCount left right)
  ≡ width
toeDecisionCountExact =
  EqualityDecision.equalityDecisionCountExact

toeOrderedWidthDoesNotLowerBoundArbitraryDecisionCount :
  ((width : Nat)
   (left right : Vec Bool width) →
   Bits.bitCardinality width
   ≤
   proj₂ (EqualityDecision.equalityDecisionWithCount left right))
  →
  ⊥
toeOrderedWidthDoesNotLowerBoundArbitraryDecisionCount =
  EqualityDecision.noOrderedWidthToDecisionCountTransfer

toeBlockEqualityConditionalDirectDPObstruction :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {width : Nat} →
  EqualityDirectDP.BlockEqualityLiveRoot state width →
  Q2.recursiveMeasure state
  ≤
  Width.triple (Bits.bitCardinality width) →
  DirectDP.DirectDPChargedConstructionRun state →
  ⊥
toeBlockEqualityConditionalDirectDPObstruction =
  EqualityDirectDP.blockEqualityMeasureBlocksDirectDPRun

toeGenericSelfSpecializationDoesNotForceSmallWidth :
  ∀ {remaining width : Nat}
    (formula : Cook.BooleanFormula) →
  Width.ResidualWidthWitness
    {root = Family.cookIndexedRestrictionRoot formula}
    remaining
    width →
  SelfSpecialization.EchoFixedPointResidualWidth remaining width
toeGenericSelfSpecializationDoesNotForceSmallWidth =
  SelfSpecialization.anyResidualWidthOccursInEchoFixedPointImage

toeCandidateHighWidthRefutesRequiredFirstStep :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    (debt : FirstStep.CandidateFirstStepCouplingDebt candidate constructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (FirstStep.initial debt))}
    remaining
    width →
  Q2.recursiveMeasure (FirstStep.initial debt)
  ≤
  Width.triple width →
  ⊥
toeCandidateHighWidthRefutesRequiredFirstStep =
  FirstStep.highWidthRefutesCandidateFirstStepCouplingDebt

toeExhaustiveBuilderFailsAtSmallBudget :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining))
    (budget : Nat) →
  budget
    ≤ Step.oneLayerEnumerationWork (Root.rootedLayer previous) →
  Work.budgetedRootedKeys (Root.descend previous) budget
    ≡
    nothing
toeExhaustiveBuilderFailsAtSmallBudget =
  Exhaustive.smallBudgetForcesExhaustiveFailure

toeCandidateOutputDoesNotDetermineFuture :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState)
    (advance : Bool → Maybe CandidateMachine.CandidateConfiguration) →
  ((configuration : CandidateMachine.CandidateConfiguration) →
    Future.candidateTransition candidate configuration
    ≡ advance (Future.candidatePresentOutput candidate configuration)) →
  ⊥
toeCandidateOutputDoesNotDetermineFuture =
  Future.candidateQuotedRootOutputTransportFails

toeStutteringPreservesDecision :
  ∀ {machine : Machine.DeterministicMachine}
    (execution : ToP.ClockedDeterministicBooleanExecution machine)
    (input : Machine.dInput machine) →
  ToP.clockedDecision (Stutter.stutteringExecution execution) input
  ≡
  ToP.clockedDecision execution input
toeStutteringPreservesDecision =
  Stutter.stutteringPreservesDecision

toeInterpreterWorkLinearBound :
  (program : List Tape.TapeInstruction) →
  (steps : Nat) →
  (configuration : Tape.TapeConfiguration) →
  Tape.runInterpreterWork program steps configuration
  ≤ Tape.linearInterpreterBudget program steps
toeInterpreterWorkLinearBound =
  Tape.runInterpreterWorkLinearBound

toeSameMachineProgramCookLevin :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Weld.SameMachineProgramCookLevinCertificate
    machine stateCoverage symbolCoverage nonempty input steps
toeSameMachineProgramCookLevin =
  Weld.sameMachineProgramCookLevinCertificate

------------------------------------------------------------------------
-- MAX-CUT RESULT.
--
-- Positive exact result:
--   literal block equality has 2^n ordered residual width.
--
-- Exact non-promotion results:
--   that width is not an arbitrary decision-time lower bound;
--   generic self-specialization does not force small width;
--   one exhaustive builder can fail without proving SAT lower bounds;
--   present output does not determine future machine state.
--
-- Exact conditional obstruction:
--   same-object high width plus a small direct-DP measure blocks that run;
--   if an independent candidate-first-step theorem requires progress on the
--   same state, high width refutes that progress.
--
-- Preserved positive infrastructure:
--   stuttering preserves decisions;
--   finite interpreter work has an explicit linear program bound;
--   finite program code and Cook--Levin use one ConcreteTapeMachine.
------------------------------------------------------------------------
