module DASHI.Cognition.PhaseEnrichedTrit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- A finite phase-bearing carrier above the observable balanced trit.
--
-- This is deliberately not advertised as a Hilbert space.  It supplies the
-- missing structural content needed for the statement that BT.zero can be an
-- observation of a non-singleton hidden fibre: three weights, a cyclic phase,
-- and a quotient selecting a uniquely dominant binding polarity.
------------------------------------------------------------------------

data Phase3 : Set where
  phase0 phase1 phase2 : Phase3

rotatePhase : Phase3 → Phase3
rotatePhase phase0 = phase1
rotatePhase phase1 = phase2
rotatePhase phase2 = phase0

rotatePhaseThree : (phase : Phase3) →
  rotatePhase (rotatePhase (rotatePhase phase)) ≡ phase
rotatePhaseThree phase0 = refl
rotatePhaseThree phase1 = refl
rotatePhaseThree phase2 = refl

record PhaseEnrichedTrit : Set where
  constructor phaseEnrichedTrit
  field
    negativeWeight : Nat
    neutralWeight  : Nat
    positiveWeight : Nat
    phase          : Phase3

open PhaseEnrichedTrit public

data NatOrdering : Set where
  less equal greater : NatOrdering

compareNat : Nat → Nat → NatOrdering
compareNat zero zero = equal
compareNat zero (suc _) = less
compareNat (suc _) zero = greater
compareNat (suc m) (suc n) = compareNat m n

strictlyGreater : Nat → Nat → Bool
strictlyGreater m n with compareNat m n
... | greater = true
... | less = false
... | equal = false

and : Bool → Bool → Bool
and true true = true
and _ _ = false

-- The quotient is negative or positive only when that polarity is uniquely
-- dominant.  Ties, neutral dominance and underdetermined profiles are all
-- observed as the non-binding trit.

observeTrit : PhaseEnrichedTrit → BT.Trit
observeTrit state with
  and
    (strictlyGreater (negativeWeight state) (neutralWeight state))
    (strictlyGreater (negativeWeight state) (positiveWeight state))
... | true = BT.neg
... | false with
  and
    (strictlyGreater (positiveWeight state) (negativeWeight state))
    (strictlyGreater (positiveWeight state) (neutralWeight state))
...   | true = BT.pos
...   | false = BT.zero

negativeDominant : PhaseEnrichedTrit
negativeDominant = phaseEnrichedTrit 5 1 2 phase0

positiveDominant : PhaseEnrichedTrit
positiveDominant = phaseEnrichedTrit 1 2 5 phase1

neutralDominant : PhaseEnrichedTrit
neutralDominant = phaseEnrichedTrit 1 5 1 phase2

balancedOpposition : PhaseEnrichedTrit
balancedOpposition = phaseEnrichedTrit 4 1 4 phase0

phaseShiftedBalancedOpposition : PhaseEnrichedTrit
phaseShiftedBalancedOpposition = phaseEnrichedTrit 4 1 4 phase1

negativeDominantObservesNegative : observeTrit negativeDominant ≡ BT.neg
negativeDominantObservesNegative = refl

positiveDominantObservesPositive : observeTrit positiveDominant ≡ BT.pos
positiveDominantObservesPositive = refl

neutralDominantObservesZero : observeTrit neutralDominant ≡ BT.zero
neutralDominantObservesZero = refl

balancedOppositionObservesZero : observeTrit balancedOpposition ≡ BT.zero
balancedOppositionObservesZero = refl

phaseShiftedBalancedObservesZero :
  observeTrit phaseShiftedBalancedOpposition ≡ BT.zero
phaseShiftedBalancedObservesZero = refl

-- The two hidden states have the same observable trit while retaining distinct
-- phase coordinates.  The significant object is therefore the zero fibre of
-- observeTrit rather than the constructor BT.zero considered in isolation.

firstZeroPhase : phase balancedOpposition ≡ phase0
firstZeroPhase = refl

secondZeroPhase : phase phaseShiftedBalancedOpposition ≡ phase1
secondZeroPhase = refl

record ZeroFibreWitness : Set where
  constructor zeroFibreWitness
  field
    hidden : PhaseEnrichedTrit
    projectsToZero : observeTrit hidden ≡ BT.zero

open ZeroFibreWitness public

zeroFromNeutralDominance : ZeroFibreWitness
zeroFromNeutralDominance = zeroFibreWitness neutralDominant refl

zeroFromBalancedOpposition : ZeroFibreWitness
zeroFromBalancedOpposition = zeroFibreWitness balancedOpposition refl

zeroFromPhaseShift : ZeroFibreWitness
zeroFromPhaseShift = zeroFibreWitness phaseShiftedBalancedOpposition refl

------------------------------------------------------------------------
-- Minimal finite interference lane.
--
-- This records that phase relation can affect the observable quotient.  It is
-- an internal algebraic model only: no Born rule, complex amplitude norm or
-- physical quantum implementation is promoted here.
------------------------------------------------------------------------

data PhaseRelation : Set where
  aligned opposed unresolved : PhaseRelation

interferenceObservation : PhaseRelation → BT.Trit
interferenceObservation aligned = BT.pos
interferenceObservation opposed = BT.zero
interferenceObservation unresolved = BT.zero

opposedPhasesRemainProjective : interferenceObservation opposed ≡ BT.zero
opposedPhasesRemainProjective = refl

alignedPhasesCanCommit : interferenceObservation aligned ≡ BT.pos
alignedPhasesCanCommit = refl
