module DASHI.Physics.Closure.NSPeriodicOffPacketRatioDerivative where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative as Packet

------------------------------------------------------------------------
-- Exact derivative of R_off = (E_total - E_packet) / E_total.
------------------------------------------------------------------------

record OffPacketDerivativeInputs
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    packet : Packet.PacketEnergyComponents Time Scalar A
    totalEnergy : Time → Scalar
    totalDifferentiable : ∀ τ →
      Calculus.Differentiable A totalEnergy τ
    totalNonzero : ∀ τ →
      Calculus.Nonzero A totalEnergy τ

open OffPacketDerivativeInputs public

offPacketEnergy :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  OffPacketDerivativeInputs Time Scalar A → Time → Scalar
offPacketEnergy {A = A} O τ =
  Calculus._-_ A
    (totalEnergy O τ)
    (Packet.packetEnergy (packet O) τ)

offPacketEnergyDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (O : OffPacketDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (offPacketEnergy O) τ
offPacketEnergyDifferentiable {A = A} O τ =
  Calculus.differentiableSubtract A
    (totalEnergy O)
    (Packet.packetEnergy (packet O))
    τ
    (totalDifferentiable O τ)
    (Packet.packetEnergyDifferentiable (packet O) τ)

offPacketEnergyDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  OffPacketDerivativeInputs Time Scalar A → Time → Scalar
offPacketEnergyDerivativeFormula {A = A} O τ =
  Calculus._-_ A
    (Calculus.derivative A (totalEnergy O) τ)
    (Packet.packetEnergyDerivativeFormula (packet O) τ)

offPacketEnergyDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (O : OffPacketDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.derivative A (offPacketEnergy O) τ ≡
  offPacketEnergyDerivativeFormula O τ
offPacketEnergyDerivative {A = A} O τ =
  trans
    (Calculus.derivativeSubtract A
      (totalEnergy O)
      (Packet.packetEnergy (packet O))
      τ
      (totalDifferentiable O τ)
      (Packet.packetEnergyDifferentiable (packet O) τ))
    (cong
      (Calculus._-_ A (Calculus.derivative A (totalEnergy O) τ))
      (Packet.packetEnergyDerivative (packet O) τ))

offPacketRatio :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  OffPacketDerivativeInputs Time Scalar A → Time → Scalar
offPacketRatio {A = A} O τ =
  Calculus._/_ A (offPacketEnergy O τ) (totalEnergy O τ)

offPacketRatioDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (O : OffPacketDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.Differentiable A (offPacketRatio O) τ
offPacketRatioDifferentiable {A = A} O τ =
  Calculus.differentiableDivide A
    (offPacketEnergy O)
    (totalEnergy O)
    τ
    (offPacketEnergyDifferentiable O τ)
    (totalDifferentiable O τ)
    (totalNonzero O τ)

offPacketRatioDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  OffPacketDerivativeInputs Time Scalar A → Time → Scalar
offPacketRatioDerivativeFormula {A = A} O τ =
  Calculus._/_ A
    (Calculus._-_ A
      (Calculus._*_ A
        (offPacketEnergyDerivativeFormula O τ)
        (totalEnergy O τ))
      (Calculus._*_ A
        (offPacketEnergy O τ)
        (Calculus.derivative A (totalEnergy O) τ)))
    (Calculus._*_ A (totalEnergy O τ) (totalEnergy O τ))

offPacketRatioDerivative :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (O : OffPacketDerivativeInputs Time Scalar A) → ∀ τ →
  Calculus.derivative A (offPacketRatio O) τ ≡
  offPacketRatioDerivativeFormula O τ
offPacketRatioDerivative {A = A} O τ =
  trans
    (Calculus.derivativeDivide A
      (offPacketEnergy O)
      (totalEnergy O)
      τ
      (offPacketEnergyDifferentiable O τ)
      (totalDifferentiable O τ)
      (totalNonzero O τ))
    (cong
      (λ offDerivative →
        Calculus._/_ A
          (Calculus._-_ A
            (Calculus._*_ A offDerivative (totalEnergy O τ))
            (Calculus._*_ A
              (offPacketEnergy O τ)
              (Calculus.derivative A (totalEnergy O) τ)))
          (Calculus._*_ A (totalEnergy O τ) (totalEnergy O τ)))
      (offPacketEnergyDerivative O τ))
