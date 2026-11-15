module DASHI.Physics.Motors.MadScience369V2DelayQueueEnergyExact where

-- Finite NONZERO-delay transport of nonnegative energy quanta.
-- A packet needs >=1 update before it reaches the remote endpoint.
-- This is a constructive queue identity, NOT a continuum Maxwell proof,
-- and it must not be mistaken for a measured @madscience369 V2 line.
-- The distinct Smith/Filsinger donor formalises retarded flight times;
-- this module formalises conservation while those packets are in transit.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

sumVec : ∀ {n} → Vec Nat n → Nat
sumVec [] = zero
sumVec (x ∷ xs) = x + sumVec xs

plusRightZero : (a : Nat) → a + zero ≡ a
plusRightZero zero = refl
plusRightZero (suc a) rewrite plusRightZero a = refl

plusSucRight : (a b : Nat) → a + suc b ≡ suc (a + b)
plusSucRight zero b = refl
plusSucRight (suc a) b rewrite plusSucRight a b = refl

plusAssoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
plusAssoc zero b c = refl
plusAssoc (suc a) b c rewrite plusAssoc a b c = refl

plusComm : (a b : Nat) → a + b ≡ b + a
plusComm zero b rewrite plusRightZero b = refl
plusComm (suc a) b rewrite plusComm a b | plusSucRight b a = refl

record StepResult (n : Nat) : Set where
  constructor result
  field
    queueAfter : Vec Nat (suc n)
    emittedEnergy : Nat

open StepResult public

-- Zero-length queues are excluded by the Vec (suc n) type.
-- Forward packets move by exactly one cell per simulation tick.
shift : ∀ {n} → Nat → Vec Nat (suc n) → StepResult n
shift input (old ∷ []) = result (input ∷ []) old
shift input (old ∷ newer ∷ rest) with shift old (newer ∷ rest)
... | result next out = result (input ∷ next) out

-- A genuine structural induction: the transit inventory after a shift
-- plus the emitted output is exactly old inventory plus new input.
shiftEnergyConserves : ∀ {n} (input : Nat) (queue : Vec Nat (suc n)) →
  sumVec (queueAfter (shift input queue)) + emittedEnergy (shift input queue)
  ≡ input + sumVec queue
shiftEnergyConserves input (old ∷ [])
  rewrite plusRightZero input | plusRightZero old = refl
shiftEnergyConserves input (old ∷ newer ∷ rest)
  with shift old (newer ∷ rest) | shiftEnergyConserves old (newer ∷ rest)
... | result next out | proof
  rewrite plusAssoc input (sumVec next) out | proof = refl

-- Nonnegative arrival cannot exceed the total currently available energy.
-- No hidden instantaneous gain is introduced by the transport queue.
emittedCannotExceedAvailable : ∀ {n} (input : Nat) (queue : Vec Nat (suc n)) →
  Bound._≤_ (emittedEnergy (shift input queue)) (input + sumVec queue)
emittedCannotExceedAvailable input queue =
  Bound.transportUpper (shiftEnergyConserves input queue)
    (Bound.transportUpper
      (plusComm (emittedEnergy (shift input queue))
                (sumVec (queueAfter (shift input queue))))
      (Bound.≤-append
        (emittedEnergy (shift input queue))
        (sumVec (queueAfter (shift input queue)))))

-- Illustration: two positive-distance cells require two shifts.
initialTwoCellQueue : Vec Nat (suc (suc zero))
initialTwoCellQueue = zero ∷ zero ∷ []

firstTick : StepResult (suc zero)
firstTick = shift 17 initialTwoCellQueue

firstTickHasNoRemoteArrival : emittedEnergy firstTick ≡ zero
firstTickHasNoRemoteArrival = refl

secondTick : StepResult (suc zero)
secondTick = shift zero (queueAfter firstTick)

secondTickArrives : emittedEnergy secondTick ≡ 17
secondTickArrives = refl

-- Kernel typecheck is mandatory before accepting this Agda source as proof.