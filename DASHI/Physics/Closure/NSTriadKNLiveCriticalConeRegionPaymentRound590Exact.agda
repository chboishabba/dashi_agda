module DASHI.Physics.Closure.NSTriadKNLiveCriticalConeRegionPaymentRound590Exact where

------------------------------------------------------------------------
-- ROUND590 / LIVE REGION PAYMENT IS THE PRIMITIVE PRODUCER
--
-- R589 reduced historical R434/R588 packaging to one R284 payment plus one
-- live-scalar decomposition equality.  The remaining scheduler still exposed
-- those as two independent sockets even though the decomposition belongs to the
-- same physical region payment.
--
-- This round makes the least-privilege producer one LIVE record indexed by the
-- literal R440 fixed-output scalar.  It carries exactly:
--
--   liveCross = (deep FL + deep HH) + critical-core Gram debt,
--   deep FL <= C_FL E D,
--   deep HH <= C_HH E D,
--   critical core <= theta Q_core + C_core E D, theta < 1.
--
-- From that record both the historical R284 payment and the R589 same-object
-- payment are compiler output.  Thus the same-object split is no longer a
-- fourth independently schedulable theorem after the three physical region
-- payments; it is part of constructing the exact live payment object itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNLiveCriticalConePaymentCompilerRound589Exact as R589
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

record LiveCriticalConeRegionPayment590
    {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode) : Set where
  constructor live-critical-cone-region-payment-590
  field
    energyDissipation590 : ℚ

    deepFarLowMass590 deepHHMass590 : ℚ
    coreCompanionMass590 coreGramDebt590 : ℚ

    deepFarLowCoefficient590 deepHHCoefficient590
      coreEDCoefficient590 theta590 : ℚ

    energyDissipationNN590 : 0ℚ ≤ energyDissipation590
    thetaNN590 : 0ℚ ≤ theta590
    thetaStrictlyBelowOne590 : theta590 < 1

    liveCrossSplits590 :
      R440.fixedOutputPhysicalCommonCross W S system output
      ≡ (deepFarLowMass590 + deepHHMass590) + coreGramDebt590

    deepFarLowPayment590 :
      deepFarLowMass590 ≤ deepFarLowCoefficient590 * energyDissipation590

    deepHHPayment590 :
      deepHHMass590 ≤ deepHHCoefficient590 * energyDissipation590

    criticalCoreRelativeCovariance590 :
      coreGramDebt590
      ≤ theta590 * coreCompanionMass590
        + coreEDCoefficient590 * energyDissipation590

open LiveCriticalConeRegionPayment590 public

toR284Payment590 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    {W S system output} →
  LiveCriticalConeRegionPayment590 {E} {I} W S system output →
  R284.CriticalConeRelativeCovariancePayment
toR284Payment590 P = record
  { R284.energyDissipation = energyDissipation590 P
  ; R284.deepFarLowMass = deepFarLowMass590 P
  ; R284.deepHHMass = deepHHMass590 P
  ; R284.coreCompanionMass = coreCompanionMass590 P
  ; R284.coreGramDebt = coreGramDebt590 P
  ; R284.deepFarLowCoefficient = deepFarLowCoefficient590 P
  ; R284.deepHHCoefficient = deepHHCoefficient590 P
  ; R284.coreEDCoefficient = coreEDCoefficient590 P
  ; R284.theta = theta590 P
  ; R284.energyDissipationNN = energyDissipationNN590 P
  ; R284.thetaNN = thetaNN590 P
  ; R284.thetaStrictlyBelowOne = thetaStrictlyBelowOne590 P
  ; R284.deepFarLowPayment = deepFarLowPayment590 P
  ; R284.deepHHPayment = deepHHPayment590 P
  ; R284.criticalCoreRelativeCovariance = criticalCoreRelativeCovariance590 P
  }

toR589LivePayment590 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    {W S system output} →
  (P : LiveCriticalConeRegionPayment590 {E} {I} W S system output) →
  R589.LiveCriticalConePayment589 W S system output
toR589LivePayment590 P =
  R589.live-critical-cone-payment-589
    (toR284Payment590 P)
    (liveCrossSplits590 P)

liveCrossBelowCriticalBudget590 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode)
    (P : LiveCriticalConeRegionPayment590 W S system output) →
  R440.fixedOutputPhysicalCommonCross W S system output
  ≤ theta590 P * coreCompanionMass590 P
    + (deepFarLowCoefficient590 P + deepHHCoefficient590 P
      + coreEDCoefficient590 P) * energyDissipation590 P
liveCrossBelowCriticalBudget590 W S system output P =
  R589.liveR440CrossBelowCriticalBudget589
    W S system output (toR589LivePayment590 P)

round590R589SeparateScalarWeldIsIndependentSchedulerDebt : Bool
round590R589SeparateScalarWeldIsIndependentSchedulerDebt = false

round590LivePartitionBelongsInsidePhysicalPayment : Bool
round590LivePartitionBelongsInsidePhysicalPayment = true

round590R284HistoricalPaymentCompilerOwned : Bool
round590R284HistoricalPaymentCompilerOwned = true

round590R589LivePaymentCompilerOwned : Bool
round590R589LivePaymentCompilerOwned = true

round590LiveRegionPaymentConstructed : Bool
round590LiveRegionPaymentConstructed = false

round590CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round590CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round590ClayPromotion : Bool
round590ClayPromotion = false

round590R589SeparateScalarWeldIsIndependentSchedulerDebtIsFalse :
  round590R589SeparateScalarWeldIsIndependentSchedulerDebt ≡ false
round590R589SeparateScalarWeldIsIndependentSchedulerDebtIsFalse = refl

round590ClayPromotionIsFalse : round590ClayPromotion ≡ false
round590ClayPromotionIsFalse = refl
