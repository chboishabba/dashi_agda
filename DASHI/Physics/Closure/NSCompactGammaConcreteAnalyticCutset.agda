module DASHI.Physics.Closure.NSCompactGammaConcreteAnalyticCutset where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaInequalityExpenditureProducer
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion
open import DASHI.Physics.Closure.NSCompactGammaExactPotentialAndPacketBalance
open import DASHI.Physics.Closure.NSCompactGammaReserveDifferentialIdentities
open import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain
open import DASHI.Physics.Closure.NSCompactGammaConcreteInequalitySynthesis

------------------------------------------------------------------------
-- Concrete analytic cutset.
--
-- This module removes the last disconnected-adapter layer between the concrete
-- packet/Gamma/off-packet owners and the Route-B expenditure theorem.  It does
-- not manufacture the remaining Fourier inequalities: those remain exactly the
-- named fields of PacketLogBarrierChainRule, PacketReserveRateDecomposition,
-- GammaFloorDifferentialData, OffPacketDifferentialData, the Bernstein leaves,
-- and the inequality integration package.
------------------------------------------------------------------------

packetExactLeafAsInequality :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (B : PacketLogBarrierChainRule A X Time)
    (D : PacketReserveRateDecomposition A X Time B)
    (positive : ∀ τ → packetEnergyPositive B τ)
    (differentiable : ∀ τ → packetEnergyDifferentiable B τ) →
  ReserveDifferentialInequalityLeaf A Time
packetExactLeafAsInequality L B D positive differentiable =
  exactReserveLeafToInequality L
    (packetReserveLeaf B D positive differentiable)

gammaExactLeafAsInequality :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (G : GammaFloorDifferentialData A Time)
    (positiveEnergy : ∀ τ → packetEnergyPositive G τ) →
  ReserveDifferentialInequalityLeaf A Time
gammaExactLeafAsInequality L G positiveEnergy =
  exactReserveLeafToInequality L
    (gammaFloorDifferentialLeaf G positiveEnergy)

offPacketExactLeafAsInequality :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (O : OffPacketDifferentialData A Time) →
  ReserveDifferentialInequalityLeaf A Time
offPacketExactLeafAsInequality L O =
  exactReserveLeafToInequality L (offPacketDifferentialLeaf O)

------------------------------------------------------------------------
-- One coherent set of concrete leaves for the selected interval.
------------------------------------------------------------------------

record ConcreteAnalyticCutset
    {t : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveInequalityLaws A)
    (Time : Set t) : Set (lsuc t) where
  field
    X : ExactPotentialArithmetic A
    initialTime finalTime : Time

    packetBarrier : PacketLogBarrierChainRule A X Time
    packetRates : PacketReserveRateDecomposition A X Time packetBarrier
    packetPositive : ∀ τ → packetEnergyPositive packetBarrier τ
    packetDifferentiable : ∀ τ → packetEnergyDifferentiable packetBarrier τ

    gammaData : GammaFloorDifferentialData A Time
    gammaEnergyPositive : ∀ τ → packetEnergyPositive gammaData τ

    offPacketData : OffPacketDifferentialData A Time

    packetFinalNonnegative :
      _≤_ A (zero A)
        (ReserveDifferentialInequalityLeaf.reserve
          (packetExactLeafAsInequality L packetBarrier packetRates
            packetPositive packetDifferentiable)
          finalTime)

    gammaFinalNonnegative :
      _≤_ A (zero A)
        (ReserveDifferentialInequalityLeaf.reserve
          (gammaExactLeafAsInequality L gammaData gammaEnergyPositive)
          finalTime)

    offPacketFinalNonnegative :
      _≤_ A (zero A)
        (ReserveDifferentialInequalityLeaf.reserve
          (offPacketExactLeafAsInequality L offPacketData)
          finalTime)

open ConcreteAnalyticCutset public

cutsetReserveLeaves :
  ∀ {t} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveInequalityLaws A}
    {Time : Set t} →
  ConcreteAnalyticCutset A L Time →
  ConcreteReserveInequalityLeaves A Time
cutsetReserveLeaves {L = L} C = record
  { initialTime = initialTime C
  ; finalTime = finalTime C
  ; packetLeaf = packetExactLeafAsInequality L
      (packetBarrier C) (packetRates C)
      (packetPositive C) (packetDifferentiable C)
  ; gammaFloorLeaf = gammaExactLeafAsInequality L
      (gammaData C) (gammaEnergyPositive C)
  ; offPacketLeaf = offPacketExactLeafAsInequality L (offPacketData C)
  ; packetFinalNonnegative = packetFinalNonnegative C
  ; gammaFinalNonnegative = gammaFinalNonnegative C
  ; offPacketFinalNonnegative = offPacketFinalNonnegative C
  }

------------------------------------------------------------------------
-- Full concrete closure data.  The only remaining endpoint inputs are the
-- actual real integration realization, the BE1--BE8 inhabitants, and the BKM
-- theorem for the selected strong-solution class.
------------------------------------------------------------------------

record ConcreteAnalyticCutsetClosure
    {t l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveInequalityLaws A)
    (C3 : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (C : ConcreteAnalyticCutset A L Time) : Set (lsuc (t ⊔ l)) where
  field
    integration :
      ConcreteInequalityIntegration A C3 (cutsetReserveLeaves C)

    weightedShellExpenditure vorticityExpenditure : Scalar A

    weightedShellBelowEnvelope :
      _≤_ A weightedShellExpenditure
        (ConcreteInequalityIntegration.coerciveEnvelopeIntegral integration)

    vorticityBelowWeightedShell :
      _≤_ A vorticityExpenditure weightedShellExpenditure

    Continuation : Set l
    invokeBKMAtEndpoint :
      _≤_ A vorticityExpenditure
        (_+_ A
          (totalReservePotential (cutsetReserveLeaves C) (initialTime C))
          (ConcreteInequalityIntegration.forcingAndDataRemainder integration)) →
      Continuation

open ConcreteAnalyticCutsetClosure public

cutsetClosureData :
  ∀ {t l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveInequalityLaws A}
    {C3 : ThreeWayAdditiveInequalityCalculus A}
    {Time : Set t}
    {C : ConcreteAnalyticCutset A L Time} →
  (D : ConcreteAnalyticCutsetClosure {l = l} A L C3 C) →
  ConcreteInequalityClosureData {l = l} A L C3
    (cutsetReserveLeaves C) (integration D)
cutsetClosureData {A = A} {L = L} {C3 = C3} {C = C} D = record
  { finalPotentialNonnegative =
      sumNonnegative L
        (sumNonnegative L
          (packetFinalNonnegative C)
          (gammaFinalNonnegative C))
        (offPacketFinalNonnegative C)
  ; weightedShellExpenditure = weightedShellExpenditure D
  ; vorticityExpenditure = vorticityExpenditure D
  ; weightedShellBelowEnvelope = weightedShellBelowEnvelope D
  ; vorticityBelowWeightedShell = vorticityBelowWeightedShell D
  ; Continuation = Continuation D
  ; invokeBKMAtEndpoint = invokeBKMAtEndpoint D
  }

concrete-cutset-finite-envelope-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C3 : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (C : ConcreteAnalyticCutset A L Time)
    (D : ConcreteAnalyticCutsetClosure {l = l} A L C3 C) →
  _≤_ A
    (ConcreteInequalityIntegration.coerciveEnvelopeIntegral (integration D))
    (_+_ A
      (totalReservePotential (cutsetReserveLeaves C) (initialTime C))
      (ConcreteInequalityIntegration.forcingAndDataRemainder (integration D)))
concrete-cutset-finite-envelope-expenditure L C3 C D =
  concrete-inequality-finite-envelope-expenditure
    L C3 (cutsetReserveLeaves C) (integration D) (cutsetClosureData D)

concrete-cutset-finite-vorticity-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C3 : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (C : ConcreteAnalyticCutset A L Time)
    (D : ConcreteAnalyticCutsetClosure {l = l} A L C3 C) →
  _≤_ A
    (vorticityExpenditure D)
    (_+_ A
      (totalReservePotential (cutsetReserveLeaves C) (initialTime C))
      (ConcreteInequalityIntegration.forcingAndDataRemainder (integration D)))
concrete-cutset-finite-vorticity-expenditure L C3 C D =
  concrete-inequality-finite-vorticity-expenditure
    L C3 (cutsetReserveLeaves C) (integration D) (cutsetClosureData D)

concrete-cutset-bkm-continuation :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C3 : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (C : ConcreteAnalyticCutset A L Time)
    (D : ConcreteAnalyticCutsetClosure {l = l} A L C3 C) →
  Continuation D
concrete-cutset-bkm-continuation L C3 C D =
  concrete-inequality-bkm-continuation
    L C3 (cutsetReserveLeaves C) (integration D) (cutsetClosureData D)
