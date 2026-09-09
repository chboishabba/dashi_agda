module DASHI.ComputerScience.FiniteBoundedSemanticDecisionExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid
import DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact as Order

------------------------------------------------------------------------
-- FINITE CLOSED-WORLD BOUNDED SEMANTIC DECISION
--
-- Over a finite explicit carrier, fixed fuel, and a Boolean observer on the
-- bounded result, exhaustive evaluation is executable.  This is intentionally
-- weaker than any universal semantic-property decider over arbitrary programs.
------------------------------------------------------------------------

BoundedBoolProperty : Set
BoundedBoolProperty = Machine.MachineState → Bool

boundedResult : Nat → Machine.MachineState → Machine.MachineState
boundedResult fuel state = Machine.runFuel fuel state

decideBounded : Nat → BoundedBoolProperty → Machine.MachineState → Bool
decideBounded fuel property state = property (boundedResult fuel state)

mapDecision :
  Nat →
  BoundedBoolProperty →
  List Machine.MachineState →
  List Bool
mapDecision fuel property [] = []
mapDecision fuel property (state ∷ states) =
  decideBounded fuel property state ∷ mapDecision fuel property states

allTrue : List Bool → Bool
allTrue [] = true
allTrue (true ∷ xs) = allTrue xs
allTrue (false ∷ xs) = false

anyTrue : List Bool → Bool
anyTrue [] = false
anyTrue (true ∷ xs) = true
anyTrue (false ∷ xs) = anyTrue xs

allSatisfyBounded :
  Nat →
  BoundedBoolProperty →
  List Machine.MachineState →
  Bool
allSatisfyBounded fuel property states =
  allTrue (mapDecision fuel property states)

anySatisfyBounded :
  Nat →
  BoundedBoolProperty →
  List Machine.MachineState →
  Bool
anySatisfyBounded fuel property states =
  anyTrue (mapDecision fuel property states)

haltedProperty : BoundedBoolProperty
haltedProperty = Machine.halted

------------------------------------------------------------------------
-- Exact finite carrier: already-certified terminating runs.
------------------------------------------------------------------------

canonicalFiniteStarts : List Machine.MachineState
canonicalFiniteStarts =
  Machine.countdownInitialState 3
  ∷ Euclid.euclidInitialState 48 18
  ∷ Order.orderInitialState 2 15 _
  ∷ Order.orderInitialState 2 21 _
  ∷ []

-- Fuel 25 is at least the exact terminating fuel of all four canonical runs.
canonicalFiniteFuel : Nat
canonicalFiniteFuel = 25

canonicalFiniteHaltingDecisions : List Bool
canonicalFiniteHaltingDecisions =
  mapDecision canonicalFiniteFuel haltedProperty canonicalFiniteStarts

canonicalFiniteHaltingDecisionsExact :
  canonicalFiniteHaltingDecisions ≡ true ∷ true ∷ true ∷ true ∷ []
canonicalFiniteHaltingDecisionsExact = refl

allCanonicalRunsHaltWithin25 :
  allSatisfyBounded canonicalFiniteFuel haltedProperty canonicalFiniteStarts ≡ true
allCanonicalRunsHaltWithin25 = refl

------------------------------------------------------------------------
-- Closed-world / universal-world firewalls.
------------------------------------------------------------------------

data FiniteBoundedDecisionIsUniversalHaltingDecider : Set where
data FiniteBoundedDecisionIsRiceTheoremCounterexample : Set where
data ExhaustiveFiniteSearchImpliesGeneralDecidability : Set where

finiteBoundedDecisionDoesNotBecomeUniversalHaltingDecider :
  FiniteBoundedDecisionIsUniversalHaltingDecider → ⊥
finiteBoundedDecisionDoesNotBecomeUniversalHaltingDecider ()

finiteBoundedDecisionDoesNotRefuteRice :
  FiniteBoundedDecisionIsRiceTheoremCounterexample → ⊥
finiteBoundedDecisionDoesNotRefuteRice ()

finiteExhaustionDoesNotBecomeGeneralDecidability :
  ExhaustiveFiniteSearchImpliesGeneralDecidability → ⊥
finiteExhaustionDoesNotBecomeGeneralDecidability ()

record FiniteBoundedSemanticDecisionBoundary : Set where
  constructor finiteBoundedSemanticDecisionBoundary
  field
    finiteCarrierExplicit : Bool
    fuelBoundExplicit : Bool
    BooleanSemanticObserverExecutable : Bool
    exhaustiveDecisionExecutable : Bool
    canonicalFourRunRegressionClosed : Bool
    universalHaltingDeciderClaimed : Bool
    riceTheoremRefuted : Bool
    arbitraryProgramSemanticDecidabilityClaimed : Bool

canonicalFiniteBoundedSemanticDecisionBoundary :
  FiniteBoundedSemanticDecisionBoundary
canonicalFiniteBoundedSemanticDecisionBoundary =
  finiteBoundedSemanticDecisionBoundary
    true true true true true false false false
