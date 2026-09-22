module DASHI.Physics.Closure.NSTriadKNCriticalStandardAnalysisReceiptsRound489Exact where

------------------------------------------------------------------------
-- ROUND489 / EXPLICIT STANDARD-ANALYSIS RECEIPTS -> R148/R104
--
-- Lean now discharges the reusable FTC, finite-measure exponent downgrade,
-- time-derivative assembly, sequential Banach--Alaoglu, and weak-* dual-norm
-- lower-semicontinuity lemmas.  Simon/Aubin--Lions itself remains an external
-- published source theorem on the selected Sobolev triple.
--
-- This module gives that source theorem and the Lean-side receipts one exact
-- Agda installation surface.  Once all three witnesses are supplied, the
-- pre-existing R148 compiler produces R104.CriticalSobolevSimonUpgrade and
-- hence the existing physical critical limit.  No new NS estimate is added.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalGalerkinSimonWeldRound104Exact as R104
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148

ConcreteSetting : Set₁
ConcreteSetting = Concrete.ConcreteGalerkinSetting lzero lzero

record CriticalStandardAnalysisReceipts489
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
    (barrier : R104.CriticalBarrierTopology S X) : Set₁ where
  field
    TimeDerivativeLFourThirdHMinusHalf489 : Set
    timeDerivativeLFourThirdHMinusHalf489 :
      TimeDerivativeLFourThirdHMinusHalf489

    SimonStrongL2HOneHalf489 : Set
    simonStrongL2HOneHalf489 : SimonStrongL2HOneHalf489

    WeakStarCriticalLiminf489 : Set
    weakStarCriticalLiminf489 : WeakStarCriticalLiminf489

open CriticalStandardAnalysisReceipts489 public

receipts489BuildR148Facts :
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 S X barrier →
  R148.StandardCriticalSimonFacts S X barrier
receipts489BuildR148Facts X barrier R = record
  { R148.TimeDerivativeHMinusHalf = TimeDerivativeLFourThirdHMinusHalf489 R
  ; R148.timeDerivativeHMinusHalf = timeDerivativeLFourThirdHMinusHalf489 R
  ; R148.StrongCriticalSimon = SimonStrongL2HOneHalf489 R
  ; R148.strongCriticalSimon = simonStrongL2HOneHalf489 R
  ; R148.WeakStarCriticalLiminf = WeakStarCriticalLiminf489 R
  ; R148.weakStarCriticalLiminf = weakStarCriticalLiminf489 R
  }

receipts489BuildR104Upgrade :
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 S X barrier →
  R104.CriticalSobolevSimonUpgrade S X barrier
receipts489BuildR104Upgrade X barrier R =
  R148.standardFactsInstantiateCriticalSobolevSimonUpgrade
    X barrier (receipts489BuildR148Facts X barrier R)

receipts489GivePhysicalCriticalLimit :
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 S X barrier →
  Critical.CriticalAubinLionsTarget
receipts489GivePhysicalCriticalLimit X barrier R =
  R148.standardFactsGivePhysicalCriticalLimit
    X barrier (receipts489BuildR148Facts X barrier R)

round489ReceiptCompilerClosed : Bool
round489ReceiptCompilerClosed = true

round489AddsNewNavierStokesEstimate : Bool
round489AddsNewNavierStokesEstimate = false

round489ConcreteSimonSourceReceiptInstalled : Bool
round489ConcreteSimonSourceReceiptInstalled = false

round489ReceiptCompilerClosedIsTrue :
  round489ReceiptCompilerClosed ≡ true
round489ReceiptCompilerClosedIsTrue = refl

round489AddsNewNavierStokesEstimateIsFalse :
  round489AddsNewNavierStokesEstimate ≡ false
round489AddsNewNavierStokesEstimateIsFalse = refl
