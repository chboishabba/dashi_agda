module DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedDirectDPChargeBridgeExact where

------------------------------------------------------------------------
-- ACTUAL DIRECT-DP RUN vs. ROOTED SOURCE-WORK LOWER BOUND
--
-- No promotion from a successful high-level construction gate to a
-- DirectDPChargedConstructionRun is made here. Instead this file states the
-- precise missing accounting obligation on THAT SAME emitted machine run:
--
--   rootedDeclaredOperationalWork(path) <= machineStepCount(run).
--
-- Once that obligation is certified by a restricted interpreter on the exact
-- candidate root, the existing charged strict inequality implies that this
-- particular rooted construction cannot succeed when declared work exhausts
-- the Q2 recursive measure.
--
-- Thus high-level work accounting and machine execution remain distinct.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work

------------------------------------------------------------------------
-- The statement is NOT a new cost model: it is a local audit of an already
-- existing typed machineExecution and its actual machineStepCount.
------------------------------------------------------------------------

record MachineTracePaysRootedWork
    {state : Q2.BoundedSelfReferenceState}
    {remaining : Nat}
    (path :
      Root.DescentPath
        (Bridge.cookToIndexed (Q2.currentFormula state))
        remaining)
    (run : DirectDP.DirectDPChargedConstructionRun state) : Set where
  field
    literalMachineTracePaysSourceWork :
      Work.rootedDeclaredOperationalWork path
      ≤
      DirectDP.machineStepCount run

open MachineTracePaysRootedWork public

------------------------------------------------------------------------
-- Even before paying the detailed trace refinement, charged execution
-- guarantees its machine step count is strictly below the current measure.
------------------------------------------------------------------------

directDPActualMachineStepsBelowMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  DirectDP.machineStepCount run
  <
  Q2.recursiveMeasure state
directDPActualMachineStepsBelowMeasure {state} run =
  NatP.≤-<-trans
    (NatP.≤-trans
      (NatP.m≤n+m
        (DirectDP.machineStepCount run)
        (Authority.arityTerminalEvaluationCellCount
          (DirectDP.candidate run)
          (DirectDP.localAdmission run)))
      (NatP.m≤m+n
        (Authority.arityTerminalEvaluationCellCount
          (DirectDP.candidate run)
          (DirectDP.localAdmission run)
          + DirectDP.machineStepCount run)
        (DirectDP.directDPAuthorityPayloadMeasure
          state
          (DirectDP.candidate run)
          (DirectDP.localAdmission run))))
    (DirectDP.machineEvaluationAndNextPayloadStrict run)

------------------------------------------------------------------------
-- Cost calibration forces a strict source-work bound on that SAME run.
------------------------------------------------------------------------

paidRootedWorkBelowMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining : Nat}
    (path :
      Root.DescentPath
        (Bridge.cookToIndexed (Q2.currentFormula state))
        remaining)
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  MachineTracePaysRootedWork path run →
  Work.rootedDeclaredOperationalWork path
  <
  Q2.recursiveMeasure state
paidRootedWorkBelowMeasure path run pays =
  NatP.≤-<-trans
    (literalMachineTracePaysSourceWork pays)
    (directDPActualMachineStepsBelowMeasure run)

------------------------------------------------------------------------
-- Explicit failure boundary: if a particular exhaustive algorithm needs
-- at least the current measure, NO honest trace of that algorithm can be a
-- charged direct-DP run. This is NOT a universal complexity lower bound.
------------------------------------------------------------------------

exhaustedRootedWorkBlocksPaidDirectDPRun :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining : Nat}
    (path :
      Root.DescentPath
        (Bridge.cookToIndexed (Q2.currentFormula state))
        remaining)
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  MachineTracePaysRootedWork path run →
  Q2.recursiveMeasure state
    ≤ Work.rootedDeclaredOperationalWork path →
  ⊥
exhaustedRootedWorkBlocksPaidDirectDPRun
    path run pays exhausted =
  NatP.<⇒≱
    (paidRootedWorkBelowMeasure path run pays)
    exhausted

------------------------------------------------------------------------
-- OPEN:
-- A genuine restricted interpreter must inhabit MachineTracePaysRootedWork
-- by proving its per-instruction execution trace covers every declared
-- enumeration, evaluation, and lookup operation. A fictional step-count
-- or machine that is preloaded with the answer CANNOT satisfy that task.
------------------------------------------------------------------------
