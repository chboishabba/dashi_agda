module Ontology.Brain.BrainVocabularySurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec)

------------------------------------------------------------------------
-- Minimal local brain-side owner surface.
-- This is intentionally theorem-thin and non-claiming: it provides a
-- typed packet/state/observable/channel vocabulary that later bridge
-- layers can consume without pretending to localize a full brain model.

record BrainPacket (n : Nat) : Set where
  constructor brainPacket
  field
    payload : Vec Nat n

record BrainState (n : Nat) : Set where
  constructor brainState
  field
    packet : BrainPacket n
    coarseLayer : Nat
    active : Bool

record BrainObservable : Set where
  constructor brainObservable
  field
    packetWidth : Nat
    layerTag : Nat
    activeFlag : Bool

record BrainChannel : Set₁ where
  field
    emit : ∀ {n} → BrainState n → Σ Nat (λ m → BrainPacket m)
    observe : ∀ {n} → BrainState n → BrainObservable
    dropoutRisk : Nat
    noiseRisk : Nat

packetOf : ∀ {n} → Vec Nat n → BrainPacket n
packetOf xs = brainPacket xs

activeByWidth : Nat → Bool
activeByWidth zero = false
activeByWidth (suc _) = true

stateOf : ∀ {n} → Vec Nat n → BrainState n
stateOf {n} xs = brainState (packetOf xs) n (activeByWidth n)

observeState : ∀ {n} → BrainState n → BrainObservable
observeState {n} st =
  brainObservable n (BrainState.coarseLayer st) (BrainState.active st)

defaultBrainChannel : BrainChannel
defaultBrainChannel = record
  { emit = λ {n} st → n , BrainState.packet st
  ; observe = observeState
  ; dropoutRisk = zero
  ; noiseRisk = zero
  }

observeState-width :
  ∀ {n} (st : BrainState n) →
  BrainObservable.packetWidth (observeState st) ≡ n
observeState-width st = refl

observeState-active-stateOf :
  ∀ {n} (xs : Vec Nat n) →
  BrainObservable.activeFlag (observeState (stateOf xs)) ≡ activeByWidth n
observeState-active-stateOf xs = refl

emit-stateOf-packet :
  ∀ {n} (xs : Vec Nat n) →
  BrainChannel.emit defaultBrainChannel (stateOf xs) ≡ (n , packetOf xs)
emit-stateOf-packet xs = refl

record BrainVocabularySurface : Set₂ where
  field
    Packet : Nat → Set
    State : Nat → Set
    Observable : Set
    Channel : Set₁
    stateFromPacket : ∀ {n} → Packet n → State n
    observeState' : ∀ {n} → State n → Observable
    channelBoundary : Channel

brainVocabularySurface : BrainVocabularySurface
brainVocabularySurface = record
  { Packet = BrainPacket
  ; State = BrainState
  ; Observable = BrainObservable
  ; Channel = BrainChannel
  ; stateFromPacket = λ {n} p →
      brainState p n (activeByWidth n)
  ; observeState' = observeState
  ; channelBoundary = defaultBrainChannel
  }
