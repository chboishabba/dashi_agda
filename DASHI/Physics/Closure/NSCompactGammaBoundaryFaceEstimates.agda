module DASHI.Physics.Closure.NSCompactGammaBoundaryFaceEstimates where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSPeriodicObservableDerivativeAlgebra as Calculus
import DASHI.Physics.Closure.NSPeriodicPacketEnergyDerivative as Packet
import DASHI.Physics.Closure.NSPeriodicGammaDerivative as Gamma
import DASHI.Physics.Closure.NSPeriodicOffPacketRatioDerivative as OffPacket
import DASHI.Physics.Closure.NSPeriodicSizeFunctionalDerivative as Size

------------------------------------------------------------------------
-- One concrete observable owner and one source/loss ledger for all four faces.
--
-- The exact derivative formulas are proved in the imported modules.  The only
-- genuinely PDE-specific leaves here are the source/loss decompositions and the
-- strict positivity of their remainders.
------------------------------------------------------------------------

record ConcreteBoundaryObservables
    (Time Scalar : Set)
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar) : Set₁ where
  field
    packet : Packet.PacketEnergyComponents Time Scalar A
    packetNonzero : ∀ τ →
      Calculus.Nonzero A (Packet.packetEnergy packet) τ

    totalEnergy : Time → Scalar
    totalDifferentiable : ∀ τ →
      Calculus.Differentiable A totalEnergy τ
    totalNonzero : ∀ τ →
      Calculus.Nonzero A totalEnergy τ

    size : Size.SizeSquaredDerivativeInputs Time Scalar A

open ConcreteBoundaryObservables public

gammaInputs :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A →
  Gamma.GammaDerivativeInputs Time Scalar A
gammaInputs B = record
  { packet = packet B
  ; packetNonzero = packetNonzero B
  }

offPacketInputs :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A →
  OffPacket.OffPacketDerivativeInputs Time Scalar A
offPacketInputs B = record
  { packet = packet B
  ; totalEnergy = totalEnergy B
  ; totalDifferentiable = totalDifferentiable B
  ; totalNonzero = totalNonzero B
  }

gammaBoundaryFunctional :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
gammaBoundaryFunctional B = Gamma.gammaFunctional (gammaInputs B)

packetBoundaryFunctional :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
packetBoundaryFunctional B = Packet.packetEnergy (packet B)

offPacketBoundaryFunctional :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
offPacketBoundaryFunctional B = OffPacket.offPacketRatio (offPacketInputs B)

sizeBoundaryFunctional :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
sizeBoundaryFunctional B = Size.sizeSquared (size B)

gammaBoundaryDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
gammaBoundaryDerivativeFormula B =
  Gamma.gammaDerivativeFormula (gammaInputs B)

packetBoundaryDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
packetBoundaryDerivativeFormula B =
  Packet.packetEnergyDerivativeFormula (packet B)

offPacketBoundaryDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
offPacketBoundaryDerivativeFormula B =
  OffPacket.offPacketRatioDerivativeFormula (offPacketInputs B)

sizeBoundaryDerivativeFormula :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar} →
  ConcreteBoundaryObservables Time Scalar A → Time → Scalar
sizeBoundaryDerivativeFormula B =
  Size.sizeSquaredDerivativeFormula (size B)

record BoundarySourceLossLedger
    {Time Scalar : Set}
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar)
    (StrictlyPositive : Scalar → Set)
    (derivativeValue : Scalar) : Set where
  field
    positiveSource nearLoss farLowLoss farHighLoss switchingLoss : Scalar

    derivativeIsSourceMinusLosses :
      derivativeValue ≡
      Calculus._-_ A positiveSource
        (Calculus._+_ A nearLoss
          (Calculus._+_ A farLowLoss
            (Calculus._+_ A farHighLoss switchingLoss)))

    strictRemainder :
      StrictlyPositive
        (Calculus._-_ A positiveSource
          (Calculus._+_ A nearLoss
            (Calculus._+_ A farLowLoss
              (Calculus._+_ A farHighLoss switchingLoss))))

open BoundarySourceLossLedger public

ledgerDerivativeStrictlyPositive :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    {StrictlyPositive : Scalar → Set} {value : Scalar} →
  BoundarySourceLossLedger A StrictlyPositive value →
  StrictlyPositive value
ledgerDerivativeStrictlyPositive L =
  subst _ (sym (derivativeIsSourceMinusLosses L)) (strictRemainder L)

record ConcreteBoundaryLedgerBundle
    {Time Scalar : Set}
    (A : Calculus.ObservableDerivativeAlgebra Time Scalar)
    (StrictlyPositive : Scalar → Set)
    (B : ConcreteBoundaryObservables Time Scalar A) : Set₁ where
  field
    gammaLedger : ∀ τ →
      BoundarySourceLossLedger A StrictlyPositive
        (gammaBoundaryDerivativeFormula B τ)

    packetLedger : ∀ τ →
      BoundarySourceLossLedger A StrictlyPositive
        (packetBoundaryDerivativeFormula B τ)

    offPacketLedger : ∀ τ →
      BoundarySourceLossLedger A StrictlyPositive
        (offPacketBoundaryDerivativeFormula B τ)

    sizeLedger : ∀ τ →
      BoundarySourceLossLedger A StrictlyPositive
        (sizeBoundaryDerivativeFormula B τ)

open ConcreteBoundaryLedgerBundle public

gammaActualDerivativeStrictlyPositive :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    {StrictlyPositive : Scalar → Set}
    {B : ConcreteBoundaryObservables Time Scalar A} →
  (L : ConcreteBoundaryLedgerBundle A StrictlyPositive B) → ∀ τ →
  StrictlyPositive
    (Calculus.derivative A (gammaBoundaryFunctional B) τ)
gammaActualDerivativeStrictlyPositive {A = A} {B = B} L τ =
  subst StrictlyPositive
    (sym (Gamma.gammaDerivative (gammaInputs B) τ))
    (ledgerDerivativeStrictlyPositive (gammaLedger L τ))

packetActualDerivativeStrictlyPositive :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    {StrictlyPositive : Scalar → Set}
    {B : ConcreteBoundaryObservables Time Scalar A} →
  (L : ConcreteBoundaryLedgerBundle A StrictlyPositive B) → ∀ τ →
  StrictlyPositive
    (Calculus.derivative A (packetBoundaryFunctional B) τ)
packetActualDerivativeStrictlyPositive {A = A} {B = B} L τ =
  subst StrictlyPositive
    (sym (Packet.packetEnergyDerivative (packet B) τ))
    (ledgerDerivativeStrictlyPositive (packetLedger L τ))

offPacketActualDerivativeStrictlyPositive :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    {StrictlyPositive : Scalar → Set}
    {B : ConcreteBoundaryObservables Time Scalar A} →
  (L : ConcreteBoundaryLedgerBundle A StrictlyPositive B) → ∀ τ →
  StrictlyPositive
    (Calculus.derivative A (offPacketBoundaryFunctional B) τ)
offPacketActualDerivativeStrictlyPositive {A = A} {B = B} L τ =
  subst StrictlyPositive
    (sym (OffPacket.offPacketRatioDerivative (offPacketInputs B) τ))
    (ledgerDerivativeStrictlyPositive (offPacketLedger L τ))

sizeActualDerivativeStrictlyPositive :
  ∀ {Time Scalar} {A : Calculus.ObservableDerivativeAlgebra Time Scalar}
    {StrictlyPositive : Scalar → Set}
    {B : ConcreteBoundaryObservables Time Scalar A} →
  (L : ConcreteBoundaryLedgerBundle A StrictlyPositive B) → ∀ τ →
  StrictlyPositive
    (Calculus.derivative A (sizeBoundaryFunctional B) τ)
sizeActualDerivativeStrictlyPositive {A = A} {B = B} L τ =
  subst StrictlyPositive
    (sym (Size.sizeSquaredDerivative (size B) τ))
    (ledgerDerivativeStrictlyPositive (sizeLedger L τ))
