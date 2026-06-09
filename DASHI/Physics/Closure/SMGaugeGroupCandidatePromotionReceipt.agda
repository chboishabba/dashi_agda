module DASHI.Physics.Closure.SMGaugeGroupCandidatePromotionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as GaugeAnomaly
import DASHI.Physics.Closure.GravitationalAnomalyCancellationReceipt as Grav
import DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt as U1Table
import DASHI.Physics.QFT.SMGaugeGroupCandidateReceipt as SMCandidate

------------------------------------------------------------------------
-- A6: SM gauge-group candidate promotion status.

data SMGaugeGroupCandidatePromotionStatus : Set where
  gaugeFactorsCandidateOnly :
    SMGaugeGroupCandidatePromotionStatus

  anomalyChecksInheritedCandidate :
    SMGaugeGroupCandidatePromotionStatus

  exactGDHREqualsGSMRemainsFalse :
    SMGaugeGroupCandidatePromotionStatus

canonicalSMGaugeGroupCandidatePromotionStatus :
  List SMGaugeGroupCandidatePromotionStatus
canonicalSMGaugeGroupCandidatePromotionStatus =
  gaugeFactorsCandidateOnly
  ∷ anomalyChecksInheritedCandidate
  ∷ exactGDHREqualsGSMRemainsFalse
  ∷ []

data SMGaugeGroupCandidatePromotionBlocker : Set where
  exactContinuousGaugeGroupMissing :
    SMGaugeGroupCandidatePromotionBlocker

  exactCarrierDerivationOfSMChargesMissing :
    SMGaugeGroupCandidatePromotionBlocker

  arbitrarySectorDHRClosureMissing :
    SMGaugeGroupCandidatePromotionBlocker

  gDHREqualsGSMIdentificationMissing :
    SMGaugeGroupCandidatePromotionBlocker

canonicalSMGaugeGroupCandidatePromotionBlockers :
  List SMGaugeGroupCandidatePromotionBlocker
canonicalSMGaugeGroupCandidatePromotionBlockers =
  exactContinuousGaugeGroupMissing
  ∷ exactCarrierDerivationOfSMChargesMissing
  ∷ arbitrarySectorDHRClosureMissing
  ∷ gDHREqualsGSMIdentificationMissing
  ∷ []

data SMGaugeGroupCandidatePromotionToken : Set where

smGaugeGroupCandidatePromotionTokenImpossibleHere :
  SMGaugeGroupCandidatePromotionToken →
  ⊥
smGaugeGroupCandidatePromotionTokenImpossibleHere ()

smGaugeGroupCandidatePromotionStatement : String
smGaugeGroupCandidatePromotionStatement =
  "U(1)_Y, SU(2)_L, and SU(3)_c are recorded as candidate gauge factors with inherited anomaly checks, but exact SM gauge-group promotion and G_DHR ~= G_SM remain false."

record SMGaugeGroupCandidatePromotionReceipt : Setω where
  field
    smGaugeGroupCandidateReceipt :
      SMCandidate.SMGaugeGroupCandidateReceipt

    allGaugeFactorsCandidate :
      SMCandidate.allGaugeFactorsCandidate smGaugeGroupCandidateReceipt
      ≡
      true

    u1yChargeTableReceipt :
      U1Table.U1YChargeAssignmentTableReceipt

    u1yTableKeepsGDHRGSMFalse :
      U1Table.gDHREqualsGSM u1yChargeTableReceipt ≡ false

    anomalyVerificationReceipt :
      GaugeAnomaly.AnomalyCancellationVerificationReceipt

    gaugeAnomalyChecksCandidate :
      GaugeAnomaly.inheritedCandidateStatus anomalyVerificationReceipt
      ≡
      true

    gravitationalAnomalyReceipt :
      Grav.GravitationalAnomalyCancellationReceipt

    gravitationalAnomalyCheckCandidate :
      Grav.inheritedCandidateStatus gravitationalAnomalyReceipt ≡ true

    status :
      List SMGaugeGroupCandidatePromotionStatus

    statusIsCanonical :
      status ≡ canonicalSMGaugeGroupCandidatePromotionStatus

    candidateGaugeGroupRecorded :
      Bool

    candidateGaugeGroupRecordedIsTrue :
      candidateGaugeGroupRecorded ≡ true

    anomalyChecksRecorded :
      Bool

    anomalyChecksRecordedIsTrue :
      anomalyChecksRecorded ≡ true

    exactPhysicalGaugeGroupPromoted :
      Bool

    exactPhysicalGaugeGroupPromotedIsFalse :
      exactPhysicalGaugeGroupPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    gDHREqualsGSM :
      Bool

    gDHREqualsGSMIsFalse :
      gDHREqualsGSM ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    blockers :
      List SMGaugeGroupCandidatePromotionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalSMGaugeGroupCandidatePromotionBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ smGaugeGroupCandidatePromotionStatement

    promotionTokens :
      List SMGaugeGroupCandidatePromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    receiptBoundary :
      List String

open SMGaugeGroupCandidatePromotionReceipt public

canonicalSMGaugeGroupCandidatePromotionReceipt :
  SMGaugeGroupCandidatePromotionReceipt
canonicalSMGaugeGroupCandidatePromotionReceipt =
  record
    { smGaugeGroupCandidateReceipt =
        SMCandidate.canonicalSMGaugeGroupCandidateReceipt
    ; allGaugeFactorsCandidate =
        refl
    ; u1yChargeTableReceipt =
        U1Table.canonicalU1YChargeAssignmentTableReceipt
    ; u1yTableKeepsGDHRGSMFalse =
        refl
    ; anomalyVerificationReceipt =
        GaugeAnomaly.canonicalAnomalyCancellationVerificationReceipt
    ; gaugeAnomalyChecksCandidate =
        refl
    ; gravitationalAnomalyReceipt =
        Grav.canonicalGravitationalAnomalyCancellationReceipt
    ; gravitationalAnomalyCheckCandidate =
        refl
    ; status =
        canonicalSMGaugeGroupCandidatePromotionStatus
    ; statusIsCanonical =
        refl
    ; candidateGaugeGroupRecorded =
        true
    ; candidateGaugeGroupRecordedIsTrue =
        refl
    ; anomalyChecksRecorded =
        true
    ; anomalyChecksRecordedIsTrue =
        refl
    ; exactPhysicalGaugeGroupPromoted =
        false
    ; exactPhysicalGaugeGroupPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; gDHREqualsGSM =
        false
    ; gDHREqualsGSMIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; blockers =
        canonicalSMGaugeGroupCandidatePromotionBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        smGaugeGroupCandidatePromotionStatement
    ; statementIsCanonical =
        refl
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; receiptBoundary =
        "The three SM gauge factors are candidate-only"
        ∷ "Gauge and gravitational anomaly checks are inherited from the SM left-handed Weyl table"
        ∷ "Exact physical gauge group, exact Standard Model, terminal promotion, and G_DHR ~= G_SM remain false"
        ∷ []
    }

smGaugeGroupCandidatePromotionKeepsGDHRGSMFalse :
  gDHREqualsGSM canonicalSMGaugeGroupCandidatePromotionReceipt ≡ false
smGaugeGroupCandidatePromotionKeepsGDHRGSMFalse =
  refl
