module DASHI.Mathematics.Complexity.Karp21StrictSATConcreteRunBidiExact where

------------------------------------------------------------------------
-- K00 separate CONCRETE TAPE integration owner.
-- This does not claim Golden --safe until its original machine/source
-- dependencies have been checked and marked safe transitively.
-- The source-written BIDI uses a Set₁/Set bridge, not Set-only PR.Iff.
--
-- Sources: Stephen Cook 1971; Leonid Levin 1973; DASHI original
-- ConcreteTapeCookLevinExactBudgetIff and strict SAT theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import DASHI.Mathematics.Complexity.Karp21StrictSATBoundedCertificateNPBoundaryExact as Bounded
import DASHI.Mathematics.Complexity.Karp21CookLevinConcreteBitWordReuseExact as K00
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Tape
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Cell
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Rules
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Runs

------------------------------------------------------------------------
-- The actual exact-budget Cook-Levin machine also consumes the SAME
-- bounded certificate. No fresh SAT carrier and no oracle.
------------------------------------------------------------------------

concreteRunToBoundedStrictSATWitness :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Runs.ExactBudgetAcceptingRun input steps →
  Bounded.BoundedStrictSATWitnessYES
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
concreteRunToBoundedStrictSATWitness
  states symbols nonempty input steps run =
  Bounded.strictSATToBoundedWitness
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
    (K00.exactRunToStrictCookSATWordAcceptance
      states symbols nonempty input steps run)

boundedStrictSATWitnessToConcreteRun :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Bounded.BoundedStrictSATWitnessYES
    (K00.guardedCookLevinBitWord states symbols nonempty input steps) →
  Runs.ExactBudgetAcceptingRun input steps
boundedStrictSATWitnessToConcreteRun
  states symbols nonempty input steps witness =
  K00.strictCookSATWordAcceptanceToRun
    states symbols nonempty input steps
    (Bounded.boundedWitnessToStrictSAT
      (K00.guardedCookLevinBitWord states symbols nonempty input steps)
      witness)

------------------------------------------------------------------------
-- Universe-correct BIDI: Runs.ExactBudgetAcceptingRun : Set₁, whereas
-- PR.Iff is defined ONLY for two Set-valued propositions.
-- Reusing PR.Iff here was ill-sorted, not a missing typeclass instance.
------------------------------------------------------------------------

record ExactRunWitnessIff (Run : Set₁) (Witness : Set) : Set₁ where
  constructor exact-run-iff
  field
    runToWitness : Run → Witness
    witnessToRun : Witness → Run

k00ConcreteTapeRunBoundedStrictSATWitnessBidi :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  ExactRunWitnessIff
    (Runs.ExactBudgetAcceptingRun input steps)
    (Bounded.BoundedStrictSATWitnessYES
      (K00.guardedCookLevinBitWord states symbols nonempty input steps))
k00ConcreteTapeRunBoundedStrictSATWitnessBidi
  states symbols nonempty input steps =
  exact-run-iff
    (concreteRunToBoundedStrictSATWitness
      states symbols nonempty input steps)
    (boundedStrictSATWitnessToConcreteRun
      states symbols nonempty input steps)
