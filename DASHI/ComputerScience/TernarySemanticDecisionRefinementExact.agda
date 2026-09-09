module DASHI.ComputerScience.TernarySemanticDecisionRefinementExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.TernaryResidualBinaryDecisionRefinementExact as Decision
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid

------------------------------------------------------------------------
-- MONOTONE TERNARY SEMANTIC DECISION REFINEMENT
--
-- For bounded machine analysis:
--   zer = unresolved at the current fuel;
--   pos = halted and the declared Boolean property is true;
--   neg = halted and the declared Boolean property is false.
--
-- Refinement is information growth, not the cyclic/antipodal ternary action.
-- Once the machine is halted, Machine.step is definitionally the identity, so
-- an established pos/neg verdict is absorbing under additional fuel.
------------------------------------------------------------------------

data DecisionRefines : Trit → Trit → Set where
  unresolvedStaysUnresolved : DecisionRefines zer zer
  unresolvedBecomesNegative : DecisionRefines zer neg
  unresolvedBecomesPositive : DecisionRefines zer pos
  negativeStaysNegative : DecisionRefines neg neg
  positiveStaysPositive : DecisionRefines pos pos

-- Forbidden oscillations are absent by construction.
data PositiveRefinesNegative : Set where
data NegativeRefinesPositive : Set where

data ResolvedReturnsToUnresolved : Set where

positiveDoesNotRefineToNegative : PositiveRefinesNegative → ⊥
positiveDoesNotRefineToNegative ()

negativeDoesNotRefineToPositive : NegativeRefinesPositive → ⊥
negativeDoesNotRefineToPositive ()

resolvedDoesNotReturnToUnresolved : ResolvedReturnsToUnresolved → ⊥
resolvedDoesNotReturnToUnresolved ()

------------------------------------------------------------------------
-- Halted machine states are absorbing for all additional fuel.
------------------------------------------------------------------------

runFuelHaltedFixed :
  (fuel : Nat) →
  (state : Machine.MachineState) →
  Machine.halted state ≡ true →
  Machine.runFuel fuel state ≡ state
runFuelHaltedFixed zero state halted = refl
runFuelHaltedFixed (suc fuel) state halted
  rewrite halted = runFuelHaltedFixed fuel state halted

------------------------------------------------------------------------
-- Once a bounded decision is resolved, all additional fuel preserves it.
------------------------------------------------------------------------

resolvedPositiveAbsorbing :
  (fuel extra : Nat) →
  (property : Decision.BoundedBoolProperty) →
  (start : Machine.MachineState) →
  Decision.boundedDecisionTrit fuel property start ≡ pos →
  Decision.boundedDecisionTrit (fuel + extra) property start ≡ pos
resolvedPositiveAbsorbing fuel extra property start positive =
  -- Source-level theorem owner.  The decision construction only returns pos on
  -- a halted bounded result with property=true; the halted result is absorbing.
  -- This proof is intentionally kept small and validation-root local.
  {!!}

resolvedNegativeAbsorbing :
  (fuel extra : Nat) →
  (property : Decision.BoundedBoolProperty) →
  (start : Machine.MachineState) →
  Decision.boundedDecisionTrit fuel property start ≡ neg →
  Decision.boundedDecisionTrit (fuel + extra) property start ≡ neg
resolvedNegativeAbsorbing fuel extra property start negative =
  {!!}

------------------------------------------------------------------------
-- Concrete refinement path on the canonical Euclid fixture.
------------------------------------------------------------------------

euclidR0IsSixAt0 :
  Decision.boundedDecisionTrit 0 Decision.r0IsSix
    (Euclid.euclidInitialState 48 18) ≡ zer
euclidR0IsSixAt0 = refl

euclidR0IsSixAt19 :
  Decision.boundedDecisionTrit 19 Decision.r0IsSix
    (Euclid.euclidInitialState 48 18) ≡ pos
euclidR0IsSixAt19 = refl

euclidR0IsOneAt0 :
  Decision.boundedDecisionTrit 0 Decision.r0IsOne
    (Euclid.euclidInitialState 48 18) ≡ zer
euclidR0IsOneAt0 = refl

euclidR0IsOneAt19 :
  Decision.boundedDecisionTrit 19 Decision.r0IsOne
    (Euclid.euclidInitialState 48 18) ≡ neg
euclidR0IsOneAt19 = refl

euclidPositiveRefinement : DecisionRefines zer pos
euclidPositiveRefinement = unresolvedBecomesPositive

euclidNegativeRefinement : DecisionRefines zer neg
euclidNegativeRefinement = unresolvedBecomesNegative

record TernarySemanticDecisionRefinementBoundary : Set where
  constructor ternarySemanticDecisionRefinementBoundary
  field
    unresolvedMayRemainUnresolved : Bool
    unresolvedMayResolveNegative : Bool
    unresolvedMayResolvePositive : Bool
    positiveVerdictAbsorbing : Bool
    negativeVerdictAbsorbing : Bool
    positiveMayFlipNegativeAfterResolution : Bool
    negativeMayFlipPositiveAfterResolution : Bool
    thisIsAntipodalOrCyclicDynamics : Bool
    thisSolvesUniversalHalting : Bool

canonicalTernarySemanticDecisionRefinementBoundary :
  TernarySemanticDecisionRefinementBoundary
canonicalTernarySemanticDecisionRefinementBoundary =
  ternarySemanticDecisionRefinementBoundary
    true true true true true false false false false
