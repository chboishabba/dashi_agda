module DASHI.Foundations.WetteFiniteDerivationCompositionExact where

------------------------------------------------------------------------
-- FINITE DERIVATION COMPOSITION
--
-- WetteFiniteDeductionTraceExact supplies proof-carrying finite derivations as
-- lists of generators.  This module equips that witness with the expected
-- identity/composition laws by reusing ordinary list concatenation and the
-- existing generic Future.run semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (_++_)

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace

------------------------------------------------------------------------
-- Sequential execution of concatenated rule lists.
------------------------------------------------------------------------

runSyntax-++ :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (left right : List (W.Generator machine)) →
  (term : W.Syntax simulation) →
  Trace.runSyntax simulation (left ++ right) term
  ≡
  Trace.runSyntax simulation right
    (Trace.runSyntax simulation left term)
runSyntax-++ simulation [] right term = refl
runSyntax-++ simulation (action ∷ rest) right term =
  runSyntax-++ simulation rest right (W.syntaxStep simulation action term)

runMachine-++ :
  (machine : W.WetteMachineSpec) →
  (left right : List (W.Generator machine)) →
  (state : W.State machine) →
  Trace.runMachine machine (left ++ right) state
  ≡
  Trace.runMachine machine right (Trace.runMachine machine left state)
runMachine-++ machine [] right state = refl
runMachine-++ machine (action ∷ rest) right state =
  runMachine-++ machine rest right (W.step machine action state)

------------------------------------------------------------------------
-- Identity and transitivity of proof-carrying finite derivability.
------------------------------------------------------------------------

identityFiniteDerivation :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (term : W.Syntax simulation) →
  Trace.FiniteDerivationWitness simulation term term
identityFiniteDerivation simulation term =
  Trace.finiteDerivationWitness [] refl

composeFiniteDerivations :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  {source middle target : W.Syntax simulation} →
  Trace.FiniteDerivationWitness simulation source middle →
  Trace.FiniteDerivationWitness simulation middle target →
  Trace.FiniteDerivationWitness simulation source target
composeFiniteDerivations simulation {source} first second =
  Trace.finiteDerivationWitness
    (Trace.actions first ++ Trace.actions second)
    (trans
      (runSyntax-++ simulation
        (Trace.actions first) (Trace.actions second) source)
      (trans
        (cong
          (Trace.runSyntax simulation (Trace.actions second))
          (Trace.reaches first))
        (Trace.reaches second)))

------------------------------------------------------------------------
-- Projection respects composition at the level of the resulting endpoint.
-- We do not claim proof-irrelevance or equality of trace witnesses: two
-- different derivations may have the same encoded endpoint.
------------------------------------------------------------------------

composedDerivationProjects :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  {source middle target : W.Syntax simulation} →
  (first : Trace.FiniteDerivationWitness simulation source middle) →
  (second : Trace.FiniteDerivationWitness simulation middle target) →
  Trace.MachineReachabilityWitness machine
    (W.encode simulation source)
    (W.encode simulation target)
composedDerivationProjects simulation first second =
  Trace.finiteDerivationProjectsToMachineReachability simulation
    (composeFiniteDerivations simulation first second)

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFiniteDerivationCompositionBoundary : Set where
  constructor wetteFiniteDerivationCompositionBoundary
  field
    reflexiveFiniteDerivationConstructed : Bool
    reflexiveFiniteDerivationConstructedIsTrue :
      reflexiveFiniteDerivationConstructed ≡ true

    transitiveFiniteDerivationConstructed : Bool
    transitiveFiniteDerivationConstructedIsTrue :
      transitiveFiniteDerivationConstructed ≡ true

    compositionUsesSameOrderedRuleTrace : Bool
    compositionUsesSameOrderedRuleTraceIsTrue :
      compositionUsesSameOrderedRuleTrace ≡ true

    sameEndpointImpliesSameProofTrace : Bool
    sameEndpointImpliesSameProofTraceIsFalse :
      sameEndpointImpliesSameProofTrace ≡ false

canonicalWetteFiniteDerivationCompositionBoundary :
  WetteFiniteDerivationCompositionBoundary
canonicalWetteFiniteDerivationCompositionBoundary =
  wetteFiniteDerivationCompositionBoundary
    true refl
    true refl
    true refl
    false refl
