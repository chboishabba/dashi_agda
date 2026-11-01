module DASHI.ComputerScience.FiniteDecisionConsumerDescentBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FiniteBoundedSemanticDecisionExact as Finite

------------------------------------------------------------------------
-- FINITE DECISION AS A CONSUMER-RELATIVE OBSERVER
--
-- A bounded Boolean semantic property induces a deterministic consumer on
-- initial machine states.  The consumer itself is always sufficient for that
-- outcome.  Coarser program-only observation need not be sufficient when input
-- state changes semantic outcome; that failure is owned separately by the
-- existing non-descent witness module.
------------------------------------------------------------------------

boundedDecisionConsumer :
  Nat →
  Finite.BoundedBoolProperty →
  Machine.MachineState →
  Bool
boundedDecisionConsumer = Finite.decideBounded

boundedDecisionConsumerSelfSufficient :
  (fuel : Nat) →
  (property : Finite.BoundedBoolProperty) →
  Descent.ConsumerSufficient
    (boundedDecisionConsumer fuel property)
    (boundedDecisionConsumer fuel property)
boundedDecisionConsumerSelfSufficient fuel property =
  Descent.consumerObserverIsSufficient
    (boundedDecisionConsumer fuel property)

boundedDecisionConsumerLeast :
  (fuel : Nat) →
  (property : Finite.BoundedBoolProperty) →
  Descent.LeastSufficientConsumerObserver
    (boundedDecisionConsumer fuel property)
boundedDecisionConsumerLeast fuel property =
  Descent.canonicalConsumerObserverIsLeast
    (boundedDecisionConsumer fuel property)

------------------------------------------------------------------------
-- Explicit refinement shape: retaining initial registers always refines the
-- program-only observer when paired with program syntax. This is structural;
-- it does not assert that program+registers are sufficient for every possible
-- consumer once memory/decoder/environment coordinates are allowed to vary.
------------------------------------------------------------------------

programObserver : Machine.MachineState → Machine.Program
programObserver = Machine.program

registerObserver : Machine.MachineState → Machine.RegisterFile
registerObserver = Machine.registers

programAndRegisterObserver :
  Machine.MachineState → Machine.Program × Machine.RegisterFile
programAndRegisterObserver =
  Observer.pairObserver programObserver registerObserver

programAndRegistersRefineProgram :
  Observer.Refines programObserver programAndRegisterObserver
programAndRegistersRefineProgram left right same
  with same
... | refl = refl

------------------------------------------------------------------------
-- Boundary: finite/executable consumer reasoning is not Rice/Turing.
------------------------------------------------------------------------

data LeastConsumerObserverIsUniversalSemanticDecider : Set where
data PairRefinementIsGloballySufficientForAllSemantics : Set where

leastConsumerObserverDoesNotBecomeUniversalSemanticDecider :
  LeastConsumerObserverIsUniversalSemanticDecider → ⊥
leastConsumerObserverDoesNotBecomeUniversalSemanticDecider ()

pairRefinementDoesNotBecomeWorldComplete :
  PairRefinementIsGloballySufficientForAllSemantics → ⊥
pairRefinementDoesNotBecomeWorldComplete ()

record FiniteDecisionConsumerDescentBoundary : Set where
  constructor finiteDecisionConsumerDescentBoundary
  field
    boundedDecisionIsConsumer : Bool
    consumerObserverSelfSufficient : Bool
    canonicalLeastConsumerObserverReused : Bool
    programRegisterPairRefinesProgram : Bool
    finiteConsumerReasoningPromotedToRiceTheorem : Bool
    pairRefinementClaimedGloballyWorldComplete : Bool

canonicalFiniteDecisionConsumerDescentBoundary :
  FiniteDecisionConsumerDescentBoundary
canonicalFiniteDecisionConsumerDescentBoundary =
  finiteDecisionConsumerDescentBoundary
    true true true true false false
