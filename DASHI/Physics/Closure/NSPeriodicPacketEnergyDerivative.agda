module DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus

------------------------------------------------------------------------
-- Exact derivative of the three-shell packet energy.
------------------------------------------------------------------------

record PacketEnergyComponents
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    lowerShell centerShell upperShell : Time → Scalar

    lowerDifferentiable : ∀ τ →
      Calculus.Differentiable A lowerShell τ
    centerDifferentiable : ∀ τ →
      Calculus.Differentiable A centerShell τ
    upperDifferentiable : ∀ τ →
      Calculus.Differentiable A upperShell τ

open PacketEnergyComponents public

packetEnergy :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  PacketEnergyComponents Time Scalar A → Time → Scalar
packetEnergy {A = A} P τ =
  Calculus._+_ A
    (lowerShell P τ)
    (Calculus._+_ A (centerShell P τ) (upperShell P τ))

packetEnergyDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : PacketEnergyComponents Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (packetEnergy P) τ
packetEnergyDifferentiable {A = A} P τ =
  Calculus.differentiableAdd A
    (lowerShell P)
    (λ t → Calculus._+_ A (centerShell P t) (upperShell P t))
    τ
    (lowerDifferentiable P τ)
    (Calculus.differentiableAdd A
      (centerShell P)
      (upperShell P)
      τ
      (centerDifferentiable P τ)
      (upperDifferentiable P τ))

packetEnergyDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  PacketEnergyComponents Time Scalar A → Time → Scalar
packetEnergyDerivativeFormula {A = A} P τ =
  Calculus._+_ A
    (Calculus.derivative A (lowerShell P) τ)
    (Calculus._+_ A
      (Calculus.derivative A (centerShell P) τ)
      (Calculus.derivative A (upperShell P) τ))

packetEnergyDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : PacketEnergyComponents Time Scalar A) → ∀ τ →
  Calculus.derivative A (packetEnergy P) τ ≡
  packetEnergyDerivativeFormula P τ
packetEnergyDerivative {A = A} P τ =
  trans
    (Calculus.derivativeAdd A
      (lowerShell P)
      (λ t → Calculus._+_ A (centerShell P t) (upperShell P t))
      τ
      (lowerDifferentiable P τ)
      (Calculus.differentiableAdd A
        (centerShell P)
        (upperShell P)
        τ
        (centerDifferentiable P τ)
        (upperDifferentiable P τ)))
    (cong
      (Calculus._+_ A (Calculus.derivative A (lowerShell P) τ))
      (Calculus.derivativeAdd A
        (centerShell P)
        (upperShell P)
        τ
        (centerDifferentiable P τ)
        (upperDifferentiable P τ)))
