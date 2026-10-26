module DASHI.Reasoning.LILADustProbeIsolationExact where

-- Sovereign-LILA upstream E8GPT owns its architecture and training code;
-- Dust authors: Dahal, Mandal, Gülbahar and Vegesna.
-- DASHI's contribution is a probe-eligibility contract for SAME-STATE
-- forward comparisons. Not a source-code refinement or performance result.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (sym; trans)

record ForwardProbeExperiment
    (Parameter Input Randomness Memory Observation : Set) : Set₁ where
  field
    parameter : Parameter
    input : Input
    randomState : Randomness
    memoryBefore : Memory
    cleanForward : Parameter → Input → Randomness → Memory → Observation
    perturbedForward : Parameter → Input → Randomness → Memory → Observation
    cleanMeasurement : Observation
    perturbedMeasurement : Observation
    cleanAtSameState :
      cleanMeasurement ≡
        cleanForward parameter input randomState memoryBefore
    perturbedAtSameState :
      perturbedMeasurement ≡
        perturbedForward parameter input randomState memoryBefore
    provenance : String

-- A paired credit comparison must be reducible to two functions of
-- one identical experimental starting state. This deliberately does
-- not assert that they have equal output; the probe is meant to differ.
sameStateMeasurementContract :
  {P I R M O : Set}
  (e : ForwardProbeExperiment P I R M O) →
  (ForwardProbeExperiment.cleanMeasurement e
     ≡ ForwardProbeExperiment.cleanForward e
       (ForwardProbeExperiment.parameter e)
       (ForwardProbeExperiment.input e)
       (ForwardProbeExperiment.randomState e)
       (ForwardProbeExperiment.memoryBefore e))
sameStateMeasurementContract e =
  ForwardProbeExperiment.cleanAtSameState e

-- Demonstrates the danger of leaving random state unspecified:
-- structurally matching inputs alone do not determine observation.
data TwoRandomStates : Set where
  state0 state1 : TwoRandomStates

randomReadout : TwoRandomStates → Bool
randomReadout state0 = false
randomReadout state1 = true

differentRandomStatesDifferentReadouts :
  (randomReadout state0 ≡ false) →
  (randomReadout state1 ≡ true)
differentRandomStatesDifferentReadouts _ = refl

-- Same treatment required for a mutable resonator memory: either
-- restore or functionalise the state. No statement about E8 geometry
-- follows merely from satisfying this measurement protocol.
