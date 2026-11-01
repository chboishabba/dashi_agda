module DASHI.Biology.ClayCrossPollinationInterfaceExact where

open import DASHI.Core.Prelude

import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.EquivariantLaplacianSectorExact as Equivariant

------------------------------------------------------------------------
-- Shared interface only: symmetry action, coarse quotient, typed transport,
-- and retained residual.  Concrete Navier--Stokes and Yang--Mills estimates
-- remain in their dedicated branches with their literal operators/constants.

record SymmetryQuotientResidualInterface : Set₁ where
  constructor symmetryQuotientResidualInterface
  field
    MicroState : Set
    CoarseState : Set
    Residual : Set
    Symmetry : Set
    observe : MicroState → CoarseState
    residual : MicroState → Residual
    act : Symmetry → MicroState → MicroState
    coarseAct : Symmetry → CoarseState → CoarseState
    observationEquivariant :
      (g : Symmetry) → (x : MicroState) →
      observe (act g x) ≡ coarseAct g (observe x)

------------------------------------------------------------------------
-- Exact quotient collision retained from oriented zero.

coarseZerosAgree :
  Zero.coarseTrit Zero.negativeZero
  ≡ Zero.coarseTrit Zero.positiveZero
coarseZerosAgree = Zero.negativeAndPositiveZeroCoarseAgree

orientedZerosRemainDistinct : ¬ (Zero.negativeZero ≡ Zero.positiveZero)
orientedZerosRemainDistinct = Zero.negativeZeroNotPositiveZero

reducedPhysicalFluctuationCount : Nat
reducedPhysicalFluctuationCount = Reduced.reducedDimension

reducedPhysicalFluctuationCountIsFiftyThree :
  reducedPhysicalFluctuationCount ≡ 53
reducedPhysicalFluctuationCountIsFiftyThree = refl

------------------------------------------------------------------------
-- Exact analytic producers that the generic interface deliberately does not
-- replace or duplicate.  These names mirror the current dedicated NS and YM
-- PR frontiers rather than inventing parallel toy proofs here.

data OutstandingProducer : Set where
  nsTorusFourierRealisation : OutstandingProducer
  nsCenteredSixThreeCommutator : OutstandingProducer
  nsComparableShellTailClosure : OutstandingProducer
  ymLiteralWilsonAtomDefect : OutstandingProducer
  ymBackgroundGaugeDefect : OutstandingProducer
  ymOneStepRGGapTransfer : OutstandingProducer

producerOwner : OutstandingProducer → Equivariant.ApplicationLane
producerOwner nsTorusFourierRealisation = Equivariant.navierStokesFourierLane
producerOwner nsCenteredSixThreeCommutator = Equivariant.navierStokesFourierLane
producerOwner nsComparableShellTailClosure = Equivariant.navierStokesFourierLane
producerOwner ymLiteralWilsonAtomDefect = Equivariant.yangMillsGaugeLane
producerOwner ymBackgroundGaugeDefect = Equivariant.yangMillsGaugeLane
producerOwner ymOneStepRGGapTransfer = Equivariant.yangMillsGaugeLane

record ClayCrossPollinationBoundary : Set where
  constructor clayCrossPollinationBoundary
  field
    genericInterfaceProvesNSCenteredCommutator : Bool
    genericInterfaceProvesNSCenteredCommutatorIsFalse :
      genericInterfaceProvesNSCenteredCommutator ≡ false

    genericInterfaceProvesYMWilsonAtomBound : Bool
    genericInterfaceProvesYMWilsonAtomBoundIsFalse :
      genericInterfaceProvesYMWilsonAtomBound ≡ false

    finiteReducedFibreSuppliesVolumeUniformMassGap : Bool
    finiteReducedFibreSuppliesVolumeUniformMassGapIsFalse :
      finiteReducedFibreSuppliesVolumeUniformMassGap ≡ false

    sharedQuotientResidualLanguageIsReusable : Bool
    sharedQuotientResidualLanguageIsReusableIsTrue :
      sharedQuotientResidualLanguage ≡ true

open ClayCrossPollinationBoundary public

canonicalClayCrossPollinationBoundary : ClayCrossPollinationBoundary
canonicalClayCrossPollinationBoundary =
  clayCrossPollinationBoundary false refl false refl false refl true refl
