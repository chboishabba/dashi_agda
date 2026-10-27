module DASHI.Unified.ResidualWidthNonPromotionTOEExact where

------------------------------------------------------------------------
-- TOE NORMALIZATION: residual-width results and exact non-promotion gates.
--
-- Reuse order:
--   1. Existing residual-width witness.
--   2. Existing same-formula linear evaluator.
--   3. Existing exhaustive-builder budget failure.
--   4. Existing future-transport no-go theorem.
--   5. Existing stuttering preservation theorem.
--   6. Existing finite-interpreter work bound.
--   7. Existing same-machine program/Cook--Levin weld.
--
-- No theorem below promotes ordered residual width to arbitrary decision time.
-- No theorem below promotes one exhaustive Q1 compiler to all SAT machines.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (Maybe)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalCandidateAbstractMachineExact as CandidateMachine
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact as EqualityWidth
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityLinearDecisionSeparationExact as EqualityDecision
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExhaustiveEnumerationCostObstructionExact as Exhaustive
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateConfigurationFutureTransportNoGoExact as Future
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
-- ZKP O — Object.
--
-- Preconditions:
--   The object is the same literal block-equality formula used by the width
--   witness and the direct evaluator.
--
-- Invariant:
--   The Shannon residual witness stays attached to that exact formula root.
--
-- Postcondition:
--   The repository exposes a literal 2^n residual-width witness.
------------------------------------------------------------------------

O-residualWidthWitness :
  (width : Nat) →
  Width.ResidualWidthWitness
    {root = EqualityWidth.blockEqualityFormula width}
    width
    (Bits.bitCardinality width)
O-residualWidthWitness =
  EqualityWidth.blockEqualityResidualWidthWitness

------------------------------------------------------------------------
-- ZKP R — Response.
--
-- Preconditions:
--   The two input vectors have the same width.
--
-- Invariant:
--   The direct evaluator computes the same Boolean value as SAT.evaluate on
--   the exact block-equality formula.
--
-- Postcondition:
--   The direct comparison count is exactly the input width.
------------------------------------------------------------------------

R-decisionMatchesSameFormula :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₁ (EqualityDecision.equalityDecisionWithCount left right)
  ≡
  SAT.evaluate
    (EqualityWidth.blockEqualityFormula width)
    (EqualityWidth.blockAssignment left right)
R-decisionMatchesSameFormula =
  EqualityDecision.linearDecisionAgreesWithBlockEqualityFormula

R-decisionCountExact :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  proj₂ (EqualityDecision.equalityDecisionWithCount left right)
  ≡ width
R-decisionCountExact =
  EqualityDecision.equalityDecisionCountExact

------------------------------------------------------------------------
-- ZKP C — Constraint.
--
-- Preconditions:
--   A proposed theorem claims ordered residual width always lower-bounds the
--   comparison count of the direct evaluator.
--
-- Invariant:
--   The witness and evaluator use the same formula family.
--
-- Postcondition:
--   The proposed universal promotion is contradictory.
------------------------------------------------------------------------

C-orderedWidthDoesNotLowerBoundArbitraryDecisionCount :
  ((width : Nat)
   (left right : Vec Bool width) →
   Bits.bitCardinality width
   ≤
   proj₂ (EqualityDecision.equalityDecisionWithCount left right))
  →
  ⊥
C-orderedWidthDoesNotLowerBoundArbitraryDecisionCount =
  EqualityDecision.noOrderedWidthToDecisionCountTransfer

------------------------------------------------------------------------
-- ZKP S — Scope.
--
-- Preconditions:
--   The constructor is the existing exhaustive rooted Shannon builder.
--   The strict budget does not exceed the latest raw child enumeration work.
--
-- Invariant:
--   Raw children are enumerated before semantic merging.
--
-- Postcondition:
--   This constructor returns nothing.
--
-- Scope rule:
--   This says nothing about a different generative quotient algorithm.
------------------------------------------------------------------------

S-exhaustiveBuilderFailsAtSmallBudget :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (Agda.Builtin.Nat.suc remaining))
    (budget : Nat) →
  budget
    ≤ Step.oneLayerEnumerationWork (Root.rootedLayer previous) →
  Work.budgetedRootedKeys (Root.descend previous) budget
    ≡
    Agda.Builtin.Maybe.nothing
S-exhaustiveBuilderFailsAtSmallBudget =
  Exhaustive.smallBudgetForcesExhaustiveFailure

------------------------------------------------------------------------
-- ZKP L — Lineage.
--
-- Preconditions:
--   The observer is only the present Boolean output of the actual candidate
--   configuration machine.
--
-- Invariant:
--   The witness uses Q2.currentFormula of the supplied candidate state.
--
-- Postcondition:
--   No next-configuration function can factor through that output alone.
------------------------------------------------------------------------

L-candidateQuotedOutputCannotDetermineFuture :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (state : Q2.BoundedSelfReferenceState)
    (advance : Bool → Maybe CandidateMachine.CandidateConfiguration) →
  ((configuration : CandidateMachine.CandidateConfiguration) →
    Future.candidateTransition candidate configuration
    ≡ advance (Future.candidatePresentOutput candidate configuration)) →
  ⊥
L-candidateQuotedOutputCannotDetermineFuture =
  Future.candidateQuotedRootOutputTransportFails

------------------------------------------------------------------------
-- ZKP P — Preservation.
--
-- Preconditions:
--   A clocked deterministic Boolean execution is supplied.
--
-- Invariant:
--   Stuttering retains the full original configuration in ready/pending form.
--
-- Postcondition:
--   The transformed execution returns the same decision.
------------------------------------------------------------------------

P-stutteringPreservesDecision :
  ∀ {machine : Machine.DeterministicMachine}
    (execution : ToP.ClockedDeterministicBooleanExecution machine)
    (input : Machine.dInput machine) →
  ToP.clockedDecision (Stutter.stutteringExecution execution) input
  ≡
  ToP.clockedDecision execution input
P-stutteringPreservesDecision =
  Stutter.stutteringPreservesDecision

------------------------------------------------------------------------
-- ZKP G — Gas / operational work.
--
-- Preconditions:
--   The finite instruction list and requested transition count are explicit.
--
-- Invariant:
--   Instruction fetch scans the finite program data.
--
-- Postcondition:
--   Total declared interpreter work is bounded by the linear program budget.
------------------------------------------------------------------------

G-interpreterWorkLinearBound :
  (program : Agda.Builtin.List.List Tape.TapeInstruction) →
  (steps : Nat) →
  (configuration : Tape.TapeConfiguration) →
  Tape.runInterpreterWork program steps configuration
  ≤ Tape.linearInterpreterBudget program steps
G-interpreterWorkLinearBound =
  Tape.runInterpreterWorkLinearBound

------------------------------------------------------------------------
-- ZKP F — Final same-object weld.
--
-- Preconditions:
--   One ConcreteTapeMachine has complete finite state/symbol coverage,
--   a nonempty rule table, one input, and one step budget.
--
-- Invariant:
--   Static program serialization and Cook--Levin use the same machine object.
--
-- Postcondition:
--   The exact finite program description and exact Cook--Levin certificate
--   are packaged together without an isomorphic-surrogate gap.
------------------------------------------------------------------------

F-sameMachineProgramCookLevin :
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
F-sameMachineProgramCookLevin =
  Weld.sameMachineProgramCookLevinCertificate

------------------------------------------------------------------------
-- TOE non-promotion summary.
--
-- Preconditions:
--   Use the exact theorem owners above.
--
-- Invariants:
--   Preserve same-object identity.
--   Preserve operational cost.
--   Preserve future semantics.
--
-- Postconditions:
--   Ordered residual width is not arbitrary decision time.
--   Exhaustive-constructor failure is not a universal SAT lower bound.
--   Present output is not a future-safe machine quotient.
--   Polynomial-overhead representation changes remain explicit.
------------------------------------------------------------------------
