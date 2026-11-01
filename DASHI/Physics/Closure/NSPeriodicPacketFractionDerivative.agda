module DASHI.Physics.Closure.NSPeriodicPacketFractionDerivative where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative as Packet

------------------------------------------------------------------------
-- Exact derivative of the scale-invariant packet fraction E_packet / E_total.
--
-- This is the replacement observable forced by the finite falsification of a
-- fixed positive absolute packet-energy floor.
------------------------------------------------------------------------

record PacketFractionDerivativeInputs
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    packet : Packet.PacketEnergyComponents Time Scalar A
    totalEnergy : Time → Scalar
    totalDifferentiable : ∀ τ →
      Calculus.Differentiable A totalEnergy τ
    totalNonzero : ∀ τ →
      Calculus.Nonzero A totalEnergy τ

open PacketFractionDerivativeInputs public

packetFraction :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  PacketFractionDerivativeInputs Time Scalar A → Time → Scalar
packetFraction {A = A} P τ =
  Calculus._/_ A
    (Packet.packetEnergy (packet P) τ)
    (totalEnergy P τ)

packetFractionDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : PacketFractionDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (packetFraction P) τ
packetFractionDifferentiable {A = A} P τ =
  Calculus.differentiableDivide A
    (Packet.packetEnergy (packet P))
    (totalEnergy P)
    τ
    (Packet.packetEnergyDifferentiable (packet P) τ)
    (totalDifferentiable P τ)
    (totalNonzero P τ)

packetFractionDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  PacketFractionDerivativeInputs Time Scalar A → Time → Scalar
packetFractionDerivativeFormula {A = A} P τ =
  Calculus._/_ A
    (Calculus._-_ A
      (Calculus._*_ A
        (Packet.packetEnergyDerivativeFormula (packet P) τ)
        (totalEnergy P τ))
      (Calculus._*_ A
        (Packet.packetEnergy (packet P) τ)
        (Calculus.derivative A (totalEnergy P) τ)))
    (Calculus._*_ A
      (totalEnergy P τ)
      (totalEnergy P τ))

packetFractionDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : PacketFractionDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.derivative A (packetFraction P) τ ≡
  packetFractionDerivativeFormula P τ
packetFractionDerivative {A = A} P τ =
  trans
    (Calculus.derivativeDivide A
      (Packet.packetEnergy (packet P))
      (totalEnergy P)
      τ
      (Packet.packetEnergyDifferentiable (packet P) τ)
      (totalDifferentiable P τ)
      (totalNonzero P τ))
    (cong
      (λ packetDerivative →
        Calculus._/_ A
          (Calculus._-_ A
            (Calculus._*_ A packetDerivative (totalEnergy P τ))
            (Calculus._*_ A
              (Packet.packetEnergy (packet P) τ)
              (Calculus.derivative A (totalEnergy P) τ)))
          (Calculus._*_ A
            (totalEnergy P τ)
            (totalEnergy P τ)))
      (Packet.packetEnergyDerivative (packet P) τ))
