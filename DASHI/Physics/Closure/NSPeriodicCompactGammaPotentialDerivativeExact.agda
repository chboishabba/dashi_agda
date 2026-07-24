module DASHI.Physics.Closure.NSPeriodicCompactGammaPotentialDerivativeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative as Packet
import DASHI.Physics.Closure.NSPeriodicGammaDerivative as Gamma
import DASHI.Physics.Closure.NSPeriodicOffPacketRatioDerivative as Off
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal differentiated compact-Gamma potential
--
--   Phi = alphaE (-log Epacket)
--       + alphaGamma (-log Gamma)
--       + alphaR Roff.
--
-- The component quotient identities already exist in the periodic concrete
-- carrier.  This module composes them with constant scaling and addition, so a
-- downstream expenditure theorem no longer accepts an unrelated function named
-- "potentialDerivative".
------------------------------------------------------------------------

record ConstantScaleDerivativeLaws
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    scaleDifferentiable : ∀ coefficient f τ →
      Calculus.Differentiable A f τ →
      Calculus.Differentiable A
        (λ t → Calculus._*_ A coefficient (f t)) τ

    derivativeScale : ∀ coefficient f τ →
      Calculus.Differentiable A f τ →
      Calculus.derivative A
        (λ t → Calculus._*_ A coefficient (f t)) τ
      ≡
      Calculus._*_ A coefficient (Calculus.derivative A f τ)

open ConstantScaleDerivativeLaws public

record CompactGammaPotentialDerivativeInputs
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    scaleLaws : ConstantScaleDerivativeLaws Time Scalar A

    gammaInputs : Gamma.GammaDerivativeInputs Time Scalar A
    offPacketInputs : Off.OffPacketDerivativeInputs Time Scalar A

    packetCoherence :
      Gamma.packet gammaInputs ≡ Off.packet offPacketInputs

    alphaEnergy alphaGamma alphaRatio : Scalar

    gammaNonzero : ∀ τ →
      Calculus.Nonzero A (Gamma.gammaFunctional gammaInputs) τ

open CompactGammaPotentialDerivativeInputs public

selectedPacket :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPotentialDerivativeInputs Time Scalar A →
  Packet.PacketEnergyComponents Time Scalar A
selectedPacket P = Gamma.packet (gammaInputs P)

packetReserve gammaReserve ratioReserve :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPotentialDerivativeInputs Time Scalar A →
  Time → Scalar
packetReserve {A = A} P τ =
  Calculus._*_ A
    (alphaEnergy P)
    (Calculus.negativeLog A (Packet.packetEnergy (selectedPacket P) τ))
gammaReserve {A = A} P τ =
  Calculus._*_ A
    (alphaGamma P)
    (Calculus.negativeLog A (Gamma.gammaFunctional (gammaInputs P) τ))
ratioReserve {A = A} P τ =
  Calculus._*_ A
    (alphaRatio P)
    (Off.offPacketRatio (offPacketInputs P) τ)

compactGammaPotential :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPotentialDerivativeInputs Time Scalar A →
  Time → Scalar
compactGammaPotential {A = A} P τ =
  Calculus._+_ A
    (packetReserve P τ)
    (Calculus._+_ A (gammaReserve P τ) (ratioReserve P τ))

packetReserveDerivativeFormula gammaReserveDerivativeFormula
  ratioReserveDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPotentialDerivativeInputs Time Scalar A →
  Time → Scalar
packetReserveDerivativeFormula {A = A} P τ =
  Calculus._*_ A
    (alphaEnergy P)
    (Calculus._/_ A
      (Calculus.negative A
        (Packet.packetEnergyDerivativeFormula (selectedPacket P) τ))
      (Packet.packetEnergy (selectedPacket P) τ))
gammaReserveDerivativeFormula {A = A} P τ =
  Calculus._*_ A
    (alphaGamma P)
    (Calculus._/_ A
      (Calculus.negative A
        (Gamma.gammaDerivativeFormula (gammaInputs P) τ))
      (Gamma.gammaFunctional (gammaInputs P) τ))
ratioReserveDerivativeFormula {A = A} P τ =
  Calculus._*_ A
    (alphaRatio P)
    (Off.offPacketRatioDerivativeFormula (offPacketInputs P) τ)

compactGammaPotentialDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  CompactGammaPotentialDerivativeInputs Time Scalar A →
  Time → Scalar
compactGammaPotentialDerivativeFormula {A = A} P τ =
  Calculus._+_ A
    (packetReserveDerivativeFormula P τ)
    (Calculus._+_ A
      (gammaReserveDerivativeFormula P τ)
      (ratioReserveDerivativeFormula P τ))

packetReserveDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ → Calculus.Differentiable A (packetReserve P) τ
packetReserveDifferentiable {A = A} P τ =
  scaleDifferentiable (scaleLaws P)
    (alphaEnergy P)
    (λ t → Calculus.negativeLog A (Packet.packetEnergy (selectedPacket P) t))
    τ
    (Calculus.differentiableNegativeLog A
      (Packet.packetEnergy (selectedPacket P)) τ
      (Packet.packetEnergyDifferentiable (selectedPacket P) τ)
      (Gamma.packetNonzero (gammaInputs P) τ))

gammaReserveDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ → Calculus.Differentiable A (gammaReserve P) τ
gammaReserveDifferentiable {A = A} P τ =
  scaleDifferentiable (scaleLaws P)
    (alphaGamma P)
    (λ t → Calculus.negativeLog A (Gamma.gammaFunctional (gammaInputs P) t))
    τ
    (Calculus.differentiableNegativeLog A
      (Gamma.gammaFunctional (gammaInputs P)) τ
      (Gamma.gammaDifferentiable (gammaInputs P) τ)
      (gammaNonzero P τ))

ratioReserveDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ → Calculus.Differentiable A (ratioReserve P) τ
ratioReserveDifferentiable {A = A} P τ =
  scaleDifferentiable (scaleLaws P)
    (alphaRatio P)
    (Off.offPacketRatio (offPacketInputs P))
    τ
    (Off.offPacketRatioDifferentiable (offPacketInputs P) τ)

packetReserveDerivativeExact :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ →
  Calculus.derivative A (packetReserve P) τ
  ≡ packetReserveDerivativeFormula P τ
packetReserveDerivativeExact {A = A} P τ =
  trans
    (derivativeScale (scaleLaws P)
      (alphaEnergy P)
      (λ t → Calculus.negativeLog A (Packet.packetEnergy (selectedPacket P) t))
      τ
      (Calculus.differentiableNegativeLog A
        (Packet.packetEnergy (selectedPacket P)) τ
        (Packet.packetEnergyDifferentiable (selectedPacket P) τ)
        (Gamma.packetNonzero (gammaInputs P) τ)))
    (cong
      (Calculus._*_ A (alphaEnergy P))
      (trans
        (Calculus.derivativeNegativeLog A
          (Packet.packetEnergy (selectedPacket P)) τ
          (Packet.packetEnergyDifferentiable (selectedPacket P) τ)
          (Gamma.packetNonzero (gammaInputs P) τ))
        (cong
          (λ derivativeValue →
            Calculus._/_ A
              (Calculus.negative A derivativeValue)
              (Packet.packetEnergy (selectedPacket P) τ))
          (Packet.packetEnergyDerivative (selectedPacket P) τ))))

gammaReserveDerivativeExact :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ →
  Calculus.derivative A (gammaReserve P) τ
  ≡ gammaReserveDerivativeFormula P τ
gammaReserveDerivativeExact {A = A} P τ =
  trans
    (derivativeScale (scaleLaws P)
      (alphaGamma P)
      (λ t → Calculus.negativeLog A (Gamma.gammaFunctional (gammaInputs P) t))
      τ
      (Calculus.differentiableNegativeLog A
        (Gamma.gammaFunctional (gammaInputs P)) τ
        (Gamma.gammaDifferentiable (gammaInputs P) τ)
        (gammaNonzero P τ)))
    (cong
      (Calculus._*_ A (alphaGamma P))
      (trans
        (Calculus.derivativeNegativeLog A
          (Gamma.gammaFunctional (gammaInputs P)) τ
          (Gamma.gammaDifferentiable (gammaInputs P) τ)
          (gammaNonzero P τ))
        (cong
          (λ derivativeValue →
            Calculus._/_ A
              (Calculus.negative A derivativeValue)
              (Gamma.gammaFunctional (gammaInputs P) τ))
          (Gamma.gammaDerivative (gammaInputs P) τ))))

ratioReserveDerivativeExact :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ →
  Calculus.derivative A (ratioReserve P) τ
  ≡ ratioReserveDerivativeFormula P τ
ratioReserveDerivativeExact {A = A} P τ =
  trans
    (derivativeScale (scaleLaws P)
      (alphaRatio P)
      (Off.offPacketRatio (offPacketInputs P)) τ
      (Off.offPacketRatioDifferentiable (offPacketInputs P) τ))
    (cong
      (Calculus._*_ A (alphaRatio P))
      (Off.offPacketRatioDerivative (offPacketInputs P) τ))

compactGammaPotentialDifferentiable :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ → Calculus.Differentiable A (compactGammaPotential P) τ
compactGammaPotentialDifferentiable {A = A} P τ =
  Calculus.differentiableAdd A
    (packetReserve P)
    (λ t → Calculus._+_ A (gammaReserve P t) (ratioReserve P t))
    τ
    (packetReserveDifferentiable P τ)
    (Calculus.differentiableAdd A
      (gammaReserve P)
      (ratioReserve P)
      τ
      (gammaReserveDifferentiable P τ)
      (ratioReserveDifferentiable P τ))

compactGammaPotentialDerivativeExact :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  (P : CompactGammaPotentialDerivativeInputs Time Scalar A) →
  ∀ τ →
  Calculus.derivative A (compactGammaPotential P) τ
  ≡ compactGammaPotentialDerivativeFormula P τ
compactGammaPotentialDerivativeExact {A = A} P τ =
  trans
    (Calculus.derivativeAdd A
      (packetReserve P)
      (λ t → Calculus._+_ A (gammaReserve P t) (ratioReserve P t))
      τ
      (packetReserveDifferentiable P τ)
      (Calculus.differentiableAdd A
        (gammaReserve P)
        (ratioReserve P)
        τ
        (gammaReserveDifferentiable P τ)
        (ratioReserveDifferentiable P τ)))
    (trans
      (cong
        (Calculus._+_ A (Calculus.derivative A (packetReserve P) τ))
        (Calculus.derivativeAdd A
          (gammaReserve P)
          (ratioReserve P)
          τ
          (gammaReserveDifferentiable P τ)
          (ratioReserveDifferentiable P τ)))
      componentNormalization)
  where
  componentNormalization :
    Calculus._+_ A
      (Calculus.derivative A (packetReserve P) τ)
      (Calculus._+_ A
        (Calculus.derivative A (gammaReserve P) τ)
        (Calculus.derivative A (ratioReserve P) τ))
    ≡ compactGammaPotentialDerivativeFormula P τ
  componentNormalization =
    trans
      (cong
        (λ packetDerivative →
          Calculus._+_ A packetDerivative
            (Calculus._+_ A
              (Calculus.derivative A (gammaReserve P) τ)
              (Calculus.derivative A (ratioReserve P) τ)))
        (packetReserveDerivativeExact P τ))
      (cong
        (Calculus._+_ A (packetReserveDerivativeFormula P τ))
        (trans
          (cong
            (λ gammaDerivative →
              Calculus._+_ A gammaDerivative
                (Calculus.derivative A (ratioReserve P) τ))
            (gammaReserveDerivativeExact P τ))
          (cong
            (Calculus._+_ A (gammaReserveDerivativeFormula P τ))
            (ratioReserveDerivativeExact P τ))))

------------------------------------------------------------------------
-- Status: the literal potential and its derivative are fixed.  The remaining
-- PDE work is to substitute the Galerkin shell identities and estimate the
-- expanded formula by the positive weighted-shell expenditure ledger.
------------------------------------------------------------------------

compactGammaPotentialDerivativeLevel : ProofLevel
compactGammaPotentialDerivativeLevel = machineChecked
