module DASHI.Physics.Closure.NSPeriodicConcreteTriadForms where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice

------------------------------------------------------------------------
-- Literal resonance, placement and reality surfaces for the concrete program.
------------------------------------------------------------------------

data TriadPlacement : Set where
  nearLowHigh nearHighLow nearHighHigh farLow farHigh : TriadPlacement

record ConcreteTriad : Set where
  field
    lowMode highMode outputMode : FourierMode
    resonance : addMode lowMode highMode ≡ outputMode
    placement : TriadPlacement

open ConcreteTriad public

record ConcreteRealityConstraint (Coefficient : Set) : Set₁ where
  field
    conjugate : Coefficient → Coefficient
    coefficient : FourierMode → Coefficient
    realField : ∀ k →
      coefficient (negateMode k) ≡ conjugate (coefficient k)

open ConcreteRealityConstraint public

record ConcreteLerayContract (Vector Scalar : Set) : Set₁ where
  field
    project : FourierMode → Vector → Vector
    dotWave : FourierMode → Vector → Scalar
    zero : Scalar
    projectedDivergenceFree : ∀ k v →
      dotWave k (project k v) ≡ zero

open ConcreteLerayContract public
