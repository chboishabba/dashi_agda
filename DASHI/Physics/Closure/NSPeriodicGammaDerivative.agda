module DASHI.Physics.Closure.NSPeriodicGammaDerivative where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative as Packet

------------------------------------------------------------------------
-- Exact quotient derivative for Gamma_K = E_K / E_packet.
------------------------------------------------------------------------

record GammaDerivativeInputs
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    packet : Packet.PacketEnergyComponents Time Scalar A
    packetNonzero : ∀ τ →
      Calculus.Nonzero A (Packet.packetEnergy packet) τ

open GammaDerivativeInputs public

gammaFunctional :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  GammaDerivativeInputs Time Scalar A → Time → Scalar
gammaFunctional {A = A} G τ =
  Calculus._/_ A
    (Packet.centerShell (packet G) τ)
    (Packet.packetEnergy (packet G) τ)

gammaDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (G : GammaDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (gammaFunctional G) τ
gammaDifferentiable {A = A} G τ =
  Calculus.differentiableDivide A
    (Packet.centerShell (packet G))
    (Packet.packetEnergy (packet G))
    τ
    (Packet.centerDifferentiable (packet G) τ)
    (Packet.packetEnergyDifferentiable (packet G) τ)
    (packetNonzero G τ)

gammaDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  GammaDerivativeInputs Time Scalar A → Time → Scalar
gammaDerivativeFormula {A = A} G τ =
  Calculus._/_ A
    (Calculus._-_ A
      (Calculus._*_ A
        (Calculus.derivative A (Packet.centerShell (packet G)) τ)
        (Packet.packetEnergy (packet G) τ))
      (Calculus._*_ A
        (Packet.centerShell (packet G) τ)
        (Packet.packetEnergyDerivativeFormula (packet G) τ)))
    (Calculus._*_ A
      (Packet.packetEnergy (packet G) τ)
      (Packet.packetEnergy (packet G) τ))

gammaDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (G : GammaDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.derivative A (gammaFunctional G) τ ≡
  gammaDerivativeFormula G τ
gammaDerivative {A = A} G τ =
  trans
    (Calculus.derivativeDivide A
      (Packet.centerShell (packet G))
      (Packet.packetEnergy (packet G))
      τ
      (Packet.centerDifferentiable (packet G) τ)
      (Packet.packetEnergyDifferentiable (packet G) τ)
      (packetNonzero G τ))
    (cong
      (λ packetDerivative →
        Calculus._/_ A
          (Calculus._-_ A
            (Calculus._*_ A
              (Calculus.derivative A
                (Packet.centerShell (packet G)) τ)
              (Packet.packetEnergy (packet G) τ))
            (Calculus._*_ A
              (Packet.centerShell (packet G) τ)
              packetDerivative))
          (Calculus._*_ A
            (Packet.packetEnergy (packet G) τ)
            (Packet.packetEnergy (packet G) τ)))
      (Packet.packetEnergyDerivative (packet G) τ))
