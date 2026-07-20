{-# OPTIONS --safe #-}
module DASHI.Core.FiniteKernelDynamics where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Core.KernelOrbit

------------------------------------------------------------------------
-- A concrete collision is exactly the data needed to certify eventual
-- periodicity.  The generic finite-state pigeonhole theorem remains separate:
-- a finite carrier implementation must construct one of these witnesses.

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

------------------------------------------------------------------------
-- Finite deterministic systems expose the enumeration and the theorem that
-- orbit search produces a collision.  This is a proof obligation, not a Bool.

record FiniteDeterministicKernel : Set₁ where
  field
    State : Set
    kernel : State → State
    enumerate : Nat → State
    cardinality : Nat
    enumeration-complete :
      ∀ s →
      Set
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
