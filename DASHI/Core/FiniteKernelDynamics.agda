{-# OPTIONS --safe #-}
module DASHI.Core.FiniteKernelDynamics where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_+_; _<_)
open import Data.Product using (_×_; _,_)

open import DASHI.Core.KernelOrbit

record OrbitCollision
  {S : Set}
  (K : S → S)
  (start : S) : Set where
  field
    preperiod : Nat
    predecessorPeriod : Nat
    collision :
      iterate (preperiod + suc predecessorPeriod) K start
        ≡ iterate preperiod K start
open OrbitCollision public

collision⇒eventualPeriodicity :
  ∀ {S : Set}
    {K : S → S}
    {start : S} →
  OrbitCollision K start →
  EventualPeriodicity K start
collision⇒eventualPeriodicity collisionWitness = record
  { preperiod = OrbitCollision.preperiod collisionWitness
  ; predecessorPeriod = OrbitCollision.predecessorPeriod collisionWitness
  ; repeats = OrbitCollision.collision collisionWitness
  }

record FiniteDeterministicKernel : Set₁ where
  field
    State : Set
    kernel : State → State
    enumerate : Nat → State
    cardinality : Nat
    enumeration-complete :
      ∀ s →
      Σ Nat (λ i → (i < cardinality) × (enumerate i ≡ s))
    every-orbit-collides :
      ∀ s → OrbitCollision kernel s
open FiniteDeterministicKernel public

finite-kernel-eventually-periodic :
  (system : FiniteDeterministicKernel) →
  ∀ s →
  EventualPeriodicity
    (FiniteDeterministicKernel.kernel system)
    s
finite-kernel-eventually-periodic system s =
  collision⇒eventualPeriodicity
    (FiniteDeterministicKernel.every-orbit-collides system s)
