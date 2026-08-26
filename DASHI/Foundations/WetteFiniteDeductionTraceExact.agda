module DASHI.Foundations.WetteFiniteDeductionTraceExact where

------------------------------------------------------------------------
-- WETTE / FINITE TRACE CROSS-POLLINATION
--
-- The fixed-generator n-step theorem in WetteConstructiveAutomatonExact is
-- useful as a regression surface, but a real formal calculus uses different
-- rule constructors along one derivation. DASHI already owns generic finite
-- command execution in GenericFuturePartitionRefinementExact, and the
-- HybridTraceSafetyExact lane already uses exactly the one-step-to-finite-trace
-- induction pattern needed here.
--
-- This module therefore does not introduce another trace engine. It reuses
-- Future.run and proves that a one-step WetteDeductionSimulation commutes over
-- any finite list of possibly different generators.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GenericFuturePartitionRefinementExact as Future
import DASHI.Foundations.WetteConstructiveAutomatonExact as W

------------------------------------------------------------------------
-- Source and machine traces use the same generic run owner.
------------------------------------------------------------------------

runSyntax :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  List (W.Generator machine) →
  W.Syntax simulation →
  W.Syntax simulation
runSyntax simulation = Future.run (W.syntaxStep simulation)

runMachine :
  (machine : W.WetteMachineSpec) →
  List (W.Generator machine) →
  W.State machine →
  W.State machine
runMachine machine = Future.run (W.step machine)

runMachine-cong :
  {machine : W.WetteMachineSpec} →
  (actions : List (W.Generator machine)) →
  {left right : W.State machine} →
  left ≡ right →
  runMachine machine actions left ≡ runMachine machine actions right
runMachine-cong [] refl = refl
runMachine-cong {machine} (action ∷ rest) equality =
  runMachine-cong rest (cong (W.step machine action) equality)

------------------------------------------------------------------------
-- Mixed-generator simulation theorem.
------------------------------------------------------------------------

finiteTraceSimulation :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (actions : List (W.Generator machine)) →
  (term : W.Syntax simulation) →
  W.encode simulation (runSyntax simulation actions term)
  ≡
  runMachine machine actions (W.encode simulation term)
finiteTraceSimulation simulation [] term = refl
finiteTraceSimulation {machine} simulation (action ∷ rest) term =
  trans
    (finiteTraceSimulation simulation rest
      (W.syntaxStep simulation action term))
    (runMachine-cong rest (W.stepCommutes simulation action term))

------------------------------------------------------------------------
-- Kernel/admissibility preservation over arbitrary finite rule traces.
--
-- This is the same generic invariant-lifting pattern used by
-- HybridTraceSafetyExact: one-step preservation is enough for every finite
-- declared command sequence.
------------------------------------------------------------------------

finiteTracePreservesAdmissible :
  (machine : W.WetteMachineSpec) →
  (actions : List (W.Generator machine)) →
  (state : W.State machine) →
  W.admissible machine state ≡ true →
  W.admissible machine (runMachine machine actions state) ≡ true
finiteTracePreservesAdmissible machine [] state admissible = admissible
finiteTracePreservesAdmissible machine (action ∷ rest) state admissible =
  finiteTracePreservesAdmissible machine rest
    (W.step machine action state)
    (W.preservesAdmissible machine action state admissible)

encodedFiniteTracePreservesAdmissible :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (actions : List (W.Generator machine)) →
  (term : W.Syntax simulation) →
  W.admissible machine (W.encode simulation term) ≡ true →
  W.admissible machine
    (W.encode simulation (runSyntax simulation actions term)) ≡ true
encodedFiniteTracePreservesAdmissible {machine} simulation actions term admissible
  rewrite finiteTraceSimulation simulation actions term =
  finiteTracePreservesAdmissible machine actions
    (W.encode simulation term) admissible

------------------------------------------------------------------------
-- Proof-carrying finite derivations.
------------------------------------------------------------------------

record FiniteDerivationWitness
  {machine : W.WetteMachineSpec}
  (simulation : W.WetteDeductionSimulation machine)
  (source target : W.Syntax simulation) : Set where
  constructor finiteDerivationWitness
  field
    actions : List (W.Generator machine)
    reaches : runSyntax simulation actions source ≡ target

open FiniteDerivationWitness public

record MachineReachabilityWitness
  (machine : W.WetteMachineSpec)
  (source target : W.State machine) : Set where
  constructor machineReachabilityWitness
  field
    machineActions : List (W.Generator machine)
    machineReaches : runMachine machine machineActions source ≡ target

open MachineReachabilityWitness public

finiteDerivationProjectsToMachineReachability :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  {source target : W.Syntax simulation} →
  FiniteDerivationWitness simulation source target →
  MachineReachabilityWitness machine
    (W.encode simulation source)
    (W.encode simulation target)
finiteDerivationProjectsToMachineReachability simulation
  {source} {target} derivation =
  machineReachabilityWitness
    (actions derivation)
    (trans
      (sym (finiteTraceSimulation simulation (actions derivation) source))
      (cong (W.encode simulation) (reaches derivation)))

------------------------------------------------------------------------
-- Optional semantic invariant on syntax.
--
-- This is deliberately weaker than a global arithmetic soundness theorem.
-- Given a predicate already proved invariant under every declared syntax rule,
-- every finite derivation preserves it. The module does not manufacture the
-- predicate, a model, or a reflection theorem.
------------------------------------------------------------------------

record SyntaxInvariant
  {machine : W.WetteMachineSpec}
  (simulation : W.WetteDeductionSimulation machine) : Set₁ where
  field
    Holds : W.Syntax simulation → Set
    stepPreserves :
      (g : W.Generator machine) →
      (term : W.Syntax simulation) →
      Holds term →
      Holds (W.syntaxStep simulation g term)

open SyntaxInvariant public

finiteDerivationPreservesInvariant :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (invariant : SyntaxInvariant simulation) →
  (actions : List (W.Generator machine)) →
  (term : W.Syntax simulation) →
  Holds invariant term →
  Holds invariant (runSyntax simulation actions term)
finiteDerivationPreservesInvariant simulation invariant [] term holds = holds
finiteDerivationPreservesInvariant {machine} simulation invariant
  (action ∷ rest) term holds =
  finiteDerivationPreservesInvariant simulation invariant rest
    (W.syntaxStep simulation action term)
    (stepPreserves invariant action term holds)

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFiniteTraceBoundary : Set where
  constructor wetteFiniteTraceBoundary
  field
    mixedRuleFiniteTraceSimulationDerived : Bool
    mixedRuleFiniteTraceSimulationDerivedIsTrue :
      mixedRuleFiniteTraceSimulationDerived ≡ true

    oneStepAdmissibilityLiftsToFiniteTrace : Bool
    oneStepAdmissibilityLiftsToFiniteTraceIsTrue :
      oneStepAdmissibilityLiftsToFiniteTrace ≡ true

    finiteSourceDerivationProjectsToMachineReachability : Bool
    finiteSourceDerivationProjectsToMachineReachabilityIsTrue :
      finiteSourceDerivationProjectsToMachineReachability ≡ true

    finiteTraceTheoremRecoversHistoricalWetteRules : Bool
    finiteTraceTheoremRecoversHistoricalWetteRulesIsFalse :
      finiteTraceTheoremRecoversHistoricalWetteRules ≡ false

    invariantPreservationIsAlreadyArithmeticSoundness : Bool
    invariantPreservationIsAlreadyArithmeticSoundnessIsFalse :
      invariantPreservationIsAlreadyArithmeticSoundness ≡ false

canonicalWetteFiniteTraceBoundary : WetteFiniteTraceBoundary
canonicalWetteFiniteTraceBoundary =
  wetteFiniteTraceBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
