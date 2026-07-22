module DASHI.Algebra.Quantum.TernaryCircuit where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.List.Base using (List; []; _∷_; map)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- A finite basis-level qutrit circuit layer.  It is a reversible permutation
-- semantics, not yet an amplitude/superposition simulator.

data QutritBasis : Set where
  qNeg : QutritBasis
  qZero : QutritBasis
  qPos : QutritBasis

basisToTrit : QutritBasis → Trit.Trit
basisToTrit qNeg = Trit.neg
basisToTrit qZero = Trit.zer
basisToTrit qPos = Trit.pos

tritToBasis : Trit.Trit → QutritBasis
tritToBasis Trit.neg = qNeg
tritToBasis Trit.zer = qZero
tritToBasis Trit.pos = qPos

basisToTrit-tritToBasis :
  ∀ t →
  basisToTrit (tritToBasis t) ≡ t
basisToTrit-tritToBasis Trit.neg = refl
basisToTrit-tritToBasis Trit.zer = refl
basisToTrit-tritToBasis Trit.pos = refl

tritToBasis-basisToTrit :
  ∀ q →
  tritToBasis (basisToTrit q) ≡ q
tritToBasis-basisToTrit qNeg = refl
tritToBasis-basisToTrit qZero = refl
tritToBasis-basisToTrit qPos = refl

cycleQutrit : QutritBasis → QutritBasis
cycleQutrit qNeg = qZero
cycleQutrit qZero = qPos
cycleQutrit qPos = qNeg

inverseCycleQutrit : QutritBasis → QutritBasis
inverseCycleQutrit qNeg = qPos
inverseCycleQutrit qZero = qNeg
inverseCycleQutrit qPos = qZero

cycle³ : ∀ q → cycleQutrit (cycleQutrit (cycleQutrit q)) ≡ q
cycle³ qNeg = refl
cycle³ qZero = refl
cycle³ qPos = refl

inverseCycleLeft :
  ∀ q →
  inverseCycleQutrit (cycleQutrit q) ≡ q
inverseCycleLeft qNeg = refl
inverseCycleLeft qZero = refl
inverseCycleLeft qPos = refl

inverseCycleRight :
  ∀ q →
  cycleQutrit (inverseCycleQutrit q) ≡ q
inverseCycleRight qNeg = refl
inverseCycleRight qZero = refl
inverseCycleRight qPos = refl

data QutritGate : Set where
  identityGate : QutritGate
  cycleGate : QutritGate
  inverseCycleGate : QutritGate

applyGate : QutritGate → QutritBasis → QutritBasis
applyGate identityGate q = q
applyGate cycleGate q = cycleQutrit q
applyGate inverseCycleGate q = inverseCycleQutrit q

inverseGate : QutritGate → QutritGate
inverseGate identityGate = identityGate
inverseGate cycleGate = inverseCycleGate
inverseGate inverseCycleGate = cycleGate

inverseGateLeft :
  ∀ g q →
  applyGate (inverseGate g) (applyGate g q) ≡ q
inverseGateLeft identityGate q = refl
inverseGateLeft cycleGate q = inverseCycleLeft q
inverseGateLeft inverseCycleGate q = inverseCycleRight q

inverseGateRight :
  ∀ g q →
  applyGate g (applyGate (inverseGate g) q) ≡ q
inverseGateRight identityGate q = refl
inverseGateRight cycleGate q = inverseCycleRight q
inverseGateRight inverseCycleGate q = inverseCycleLeft q

data QutritCircuit : Set where
  halt : QutritCircuit
  applyThen : QutritGate → QutritCircuit → QutritCircuit

runCircuit : QutritCircuit → QutritBasis → QutritBasis
runCircuit halt q = q
runCircuit (applyThen g rest) q = runCircuit rest (applyGate g q)

appendCircuit : QutritCircuit → QutritCircuit → QutritCircuit
appendCircuit halt right = right
appendCircuit (applyThen g left) right =
  applyThen g (appendCircuit left right)

reverseCircuit : QutritCircuit → QutritCircuit
reverseCircuit halt = halt
reverseCircuit (applyThen g rest) =
  appendCircuit (reverseCircuit rest) (applyThen (inverseGate g) halt)

QutritRegister : Set
QutritRegister = List QutritBasis

applyGateToRegister : QutritGate → QutritRegister → QutritRegister
applyGateToRegister g = map (applyGate g)

runCircuitOnRegister : QutritCircuit → QutritRegister → QutritRegister
runCircuitOnRegister halt qs = qs
runCircuitOnRegister (applyThen g rest) qs =
  runCircuitOnRegister rest (applyGateToRegister g qs)

record FiniteQutritPermutationSemantics : Set₁ where
  field
    basis : Set
    gate : Set
    apply : gate → basis → basis
    inverse : gate → gate
    inverseLeft : ∀ g q → apply (inverse g) (apply g q) ≡ q
    inverseRight : ∀ g q → apply g (apply (inverse g) q) ≡ q

open FiniteQutritPermutationSemantics public

canonicalFiniteQutritPermutationSemantics :
  FiniteQutritPermutationSemantics
canonicalFiniteQutritPermutationSemantics =
  record
    { basis = QutritBasis
    ; gate = QutritGate
    ; apply = applyGate
    ; inverse = inverseGate
    ; inverseLeft = inverseGateLeft
    ; inverseRight = inverseGateRight
    }
