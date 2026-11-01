module Ontology.BrainComputer.BrainComputerCrossoverSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; BrainPacket; brainState)

------------------------------------------------------------------------
-- First bounded brain/computer crossover surface.

record ComputerState (n : Nat) : Set where
  constructor computerState
  field
    memory : Vec Nat n
    clock : Nat

brainInfoNorm : ∀ {n} → BrainState n → Nat
brainInfoNorm {n} _ = n

computerInfoNorm : ∀ {n} → ComputerState n → Nat
computerInfoNorm {n} _ = n

E_comp : ∀ {n} → BrainState n → ComputerState n
E_comp st =
  computerState
    (BrainPacket.payload (BrainState.packet st))
    (BrainState.coarseLayer st)

encodingNonAmplifying :
  ∀ {n} (st : BrainState n) →
  computerInfoNorm (E_comp st) ≡ brainInfoNorm st
encodingNonAmplifying st = refl

stepBrain : ∀ {n} → BrainState n → BrainState n
stepBrain st = st

stepComp : ∀ {n} → ComputerState n → ComputerState n
stepComp st = st

executionCoherent :
  ∀ {n} (st : BrainState n) →
  stepComp (E_comp st) ≡ E_comp (stepBrain st)
executionCoherent st = refl

record BrainComputerCrossoverSurface : Set₁ where
  field
    Computer : Nat → Set
    encode : ∀ {n} → BrainState n → Computer n
    brainNorm : ∀ {n} → BrainState n → Nat
    computerNorm : ∀ {n} → Computer n → Nat
    nonAmplifying :
      ∀ {n} (st : BrainState n) →
      computerNorm (encode st) ≡ brainNorm st
    brainStep : ∀ {n} → BrainState n → BrainState n
    computerStep : ∀ {n} → Computer n → Computer n
    stepSquare :
      ∀ {n} (st : BrainState n) →
      computerStep (encode st) ≡ encode (brainStep st)

brainComputerCrossoverSurface : BrainComputerCrossoverSurface
brainComputerCrossoverSurface = record
  { Computer = ComputerState
  ; encode = E_comp
  ; brainNorm = brainInfoNorm
  ; computerNorm = computerInfoNorm
  ; nonAmplifying = encodingNonAmplifying
  ; brainStep = stepBrain
  ; computerStep = stepComp
  ; stepSquare = executionCoherent
  }
