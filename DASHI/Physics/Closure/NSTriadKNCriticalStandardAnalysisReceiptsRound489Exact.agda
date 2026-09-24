module DASHI.Physics.Closure.NSTriadKNCriticalStandardAnalysisReceiptsRound489Exact where

------------------------------------------------------------------------
-- ROUND489 / DEPENDENT STANDARD-ANALYSIS RECEIPTS -> R148/R104
--
-- Lean discharges the reusable FTC, finite-measure exponent downgrade,
-- time-derivative assembly, sequential Banach--Alaoglu, and weak-* dual-norm
-- lower-semicontinuity lemmas. Simon/Aubin--Lions itself remains an external
-- published source theorem on the selected Sobolev triple.
--
-- This revision makes the receipt predicates DEPEND on the exact concrete
-- setting S, nonlinear-limit certificate X, and critical barrier topology.
-- The bridge therefore can no longer accept three unrelated arbitrary Sets.
--
-- R148/R104 retain their historical generic Set-valued interfaces for source
-- compatibility, but the Sets installed into them here are definitionally the
-- selected dependent predicates applied to S/X/barrier.
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

------------------------------------------------------------------------
-- Typed proposition families.
------------------------------------------------------------------------

record CriticalStandardAnalysisPredicates489 : Set₂ where
  field
    UniformTimeDerivativeLFourThirdHMinusHalf :
      (S : ConcreteSetting) →
      (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
      R104.CriticalBarrierTopology S X → Set

    StrongL2HOneHalfSubsequence :
      (S : ConcreteSetting) →
      (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
      R104.CriticalBarrierTopology S X → Set

    WeakStarCriticalNormLiminf :
      (S : ConcreteSetting) →
      (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
      R104.CriticalBarrierTopology S X → Set

open CriticalStandardAnalysisPredicates489 public

record CriticalStandardAnalysisReceipts489
    (P : CriticalStandardAnalysisPredicates489)
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
    (barrier : R104.CriticalBarrierTopology S X) : Set₁ where
  field
    timeDerivativeLFourThirdHMinusHalf489 :
      UniformTimeDerivativeLFourThirdHMinusHalf P S X barrier

    simonStrongL2HOneHalf489 :
      StrongL2HOneHalfSubsequence P S X barrier

    weakStarCriticalLiminf489 :
      WeakStarCriticalNormLiminf P S X barrier

open CriticalStandardAnalysisReceipts489 public

------------------------------------------------------------------------
-- The dependent predicates are preserved definitionally through R148.
------------------------------------------------------------------------

receipts489BuildR148Facts :
  (P : CriticalStandardAnalysisPredicates489) →
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 P S X barrier →
  R148.StandardCriticalSimonFacts S X barrier
receipts489BuildR148Facts P X barrier R = record
  { R148.TimeDerivativeHMinusHalf =
      UniformTimeDerivativeLFourThirdHMinusHalf P _ X barrier
  ; R148.timeDerivativeHMinusHalf =
      timeDerivativeLFourThirdHMinusHalf489 R
  ; R148.StrongCriticalSimon =
      StrongL2HOneHalfSubsequence P _ X barrier
  ; R148.strongCriticalSimon =
      simonStrongL2HOneHalf489 R
  ; R148.WeakStarCriticalLiminf =
      WeakStarCriticalNormLiminf P _ X barrier
  ; R148.weakStarCriticalLiminf =
      weakStarCriticalLiminf489 R
  }

receipts489BuildR104Upgrade :
  (P : CriticalStandardAnalysisPredicates489) →
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 P S X barrier →
  R104.CriticalSobolevSimonUpgrade S X barrier
receipts489BuildR104Upgrade P X barrier R =
  R148.standardFactsInstantiateCriticalSobolevSimonUpgrade
    X barrier (receipts489BuildR148Facts P X barrier R)

receipts489GivePhysicalCriticalLimit :
  (P : CriticalStandardAnalysisPredicates489) →
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : R104.CriticalBarrierTopology S X) →
  CriticalStandardAnalysisReceipts489 P S X barrier →
  Critical.CriticalAubinLionsTarget
receipts489GivePhysicalCriticalLimit P X barrier R =
  R148.standardFactsGivePhysicalCriticalLimit
    X barrier (receipts489BuildR148Facts P X barrier R)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round489ReceiptCompilerClosed : Bool
round489ReceiptCompilerClosed = true

round489ReceiptsIndexedByConcreteObjects : Bool
round489ReceiptsIndexedByConcreteObjects = true

round489ArbitraryUnrelatedReceiptSetsAccepted : Bool
round489ArbitraryUnrelatedReceiptSetsAccepted = false

round489AddsNewNavierStokesEstimate : Bool
round489AddsNewNavierStokesEstimate = false

round489ConcreteSimonSourceReceiptInstalled : Bool
round489ConcreteSimonSourceReceiptInstalled = false

round489ReceiptCompilerClosedIsTrue :
  round489ReceiptCompilerClosed ≡ true
round489ReceiptCompilerClosedIsTrue = refl

round489ReceiptsIndexedByConcreteObjectsIsTrue :
  round489ReceiptsIndexedByConcreteObjects ≡ true
round489ReceiptsIndexedByConcreteObjectsIsTrue = refl

round489ArbitraryUnrelatedReceiptSetsAcceptedIsFalse :
  round489ArbitraryUnrelatedReceiptSetsAccepted ≡ false
round489ArbitraryUnrelatedReceiptSetsAcceptedIsFalse = refl

round489AddsNewNavierStokesEstimateIsFalse :
  round489AddsNewNavierStokesEstimate ≡ false
round489AddsNewNavierStokesEstimateIsFalse = refl
