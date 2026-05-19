module DASHI.Physics.Closure.ReceiptFromObservableSignature where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACSS
import DASHI.Physics.Closure.ArithmeticDistortionBudget as ADB
import DASHI.Physics.Closure.DeltaQuadraticDistortion as DQD
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.ExecutionContract as EC
import DASHI.Physics.Closure.ExecutionContractLaws as ECL
import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
import DASHI.Physics.Closure.ObservableTransportGaugeEntry as OTGE

------------------------------------------------------------------------
-- Receipt bridge for the inhabited observable/signature promotion gate.
--
-- The execution receipt is still supplied by the execution layer.  This module
-- attaches the physics promotion evidence and status bits to that receipt.

record ObservableSignatureExecutionReceipt
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  (x x' : EC.State C)
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract)
  (p : OTGE.PhysicsCarrier obsCarriers)
    : Set
        (lsuc
          (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔
           ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC ⊔ ℓB ⊔
           ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓSG ⊔ ℓOB ⊔ ℓR)) where
  field
    executionReceipt :
      ECL.ExecutionContractReceipt C x x'

    promotionPoint :
      OSPT.PromotionReadyPressurePoint test p

    distortionBudget :
      Set

    observableStatus :
      OTGE.GaugeEntryStatus

    signatureStatus :
      ACSS.SignatureStressStatus

    pressureStatus :
      OSPT.PhysicsPressureStatus

    admissibleButNotNecessarilyPromoted :
      ⊤

open ObservableSignatureExecutionReceipt public

receiptFromObservableSignature :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C}
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  {test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract}
  {p : OTGE.PhysicsCarrier obsCarriers} →
  ECL.ExecutionContractReceipt C x x' →
  OSPT.PromotionReadyPressurePoint test p →
  Set →
  ObservableSignatureExecutionReceipt C x x' test p
receiptFromObservableSignature {test = test} {p = p}
  executionReceipt promotionPoint distortionBudget =
  record
    { executionReceipt = executionReceipt
    ; promotionPoint = promotionPoint
    ; distortionBudget = distortionBudget
    ; observableStatus =
        OTGE.status (OSPT.observableGate test) p
    ; signatureStatus =
        ACSS.status (OSPT.signatureStress test) (OSPT.alignState test p)
    ; pressureStatus =
        OSPT.pressureStatus test p
    ; admissibleButNotNecessarilyPromoted = tt
    }

record PairSupportObservableSignatureExecutionReceipt
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  (x x' : EC.State C)
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract)
  (p : OTGE.PhysicsCarrier obsCarriers)
  (pair : DQ.DeltaPair)
    : Set
        (lsuc
          (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔
           ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC ⊔ ℓB ⊔
           ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓSG ⊔ ℓOB ⊔ ℓR)) where
  field
    observableSignatureReceipt :
      ObservableSignatureExecutionReceipt C x x' test p

    pairSupportBudget :
      ADB.PairSupportDistortionBudget pair

open PairSupportObservableSignatureExecutionReceipt public

receiptFromObservableSignatureWithPairSupport :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C}
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  {test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract}
  {p : OTGE.PhysicsCarrier obsCarriers} →
  ECL.ExecutionContractReceipt C x x' →
  OSPT.PromotionReadyPressurePoint test p →
  (pair : DQ.DeltaPair) →
  PairSupportObservableSignatureExecutionReceipt C x x' test p pair
receiptFromObservableSignatureWithPairSupport
  {test = test} {p = p}
  executionReceipt promotionPoint pair =
  record
    { observableSignatureReceipt =
        receiptFromObservableSignature
          executionReceipt
          promotionPoint
          (ADB.PairSupportDistortionBudget pair)
    ; pairSupportBudget = ADB.pairSupportDistortionBudget pair
    }

record ObservableSignatureStatusReceipt
  {ℓS : Level}
  (State : Set ℓS)
    : Set (lsuc ℓS) where
  field
    state :
      State

    distortion :
      DQD.DeltaQuadraticDistortion State

    observableStatus :
      OTGE.GaugeEntryStatus

    signatureStatus :
      ACSS.SignatureStressStatus

    pressureStatus :
      OSPT.PhysicsPressureStatus

open ObservableSignatureStatusReceipt public

record ObservableSignaturePressureReport
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract)
  (p : OTGE.PhysicsCarrier obsCarriers)
    : Set
        (lsuc
          (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔
           ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC ⊔ ℓB ⊔
           ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓSG ⊔ ℓOB ⊔ ℓR)) where
  field
    controlPressurePoint :
      OTGE.PhysicsCarrier obsCarriers

    observableStatus :
      OTGE.GaugeEntryStatus

    signatureStatus :
      ACSS.SignatureStressStatus

    pressureStatus :
      OSPT.PhysicsPressureStatus

open ObservableSignaturePressureReport public

pressureReportFromObservableSignature :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}}
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  {test :
    OSPT.ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract}
  {p : OTGE.PhysicsCarrier obsCarriers} →
  ObservableSignaturePressureReport C test p
pressureReportFromObservableSignature {test = test} {p = p} = record
  { controlPressurePoint = p
  ; observableStatus = OTGE.status (OSPT.observableGate test) p
  ; signatureStatus =
      ACSS.status (OSPT.signatureStress test) (OSPT.alignState test p)
  ; pressureStatus = OSPT.pressureStatus test p
  }
