module DASHI.Governance.IRISDenaSameObjectAcquisitionMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact as Command
import DASHI.Governance.IRISDenaPublicRecordCeilingAndFOIExact as Public
import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.IRISDenaIranContraOpacityNonanalogyExact as NonAnalogy
import DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact as Sovereignty

------------------------------------------------------------------------
-- IRIS DENA SAME-OBJECT MAX-CUT
--
-- Paid public evidence narrows the fibre, but does not reconstruct the exact
-- individual duties.  Acquisition proceeds from cheapest primary verification
-- to increasingly operational same-object records.
------------------------------------------------------------------------

data AcquisitionStage : Set where
  correctionAwareHansard : AcquisitionStage
  embeddingProtocol : AcquisitionStage
  watchDutyAssignment : AcquisitionStage
  operationalActionLog : AcquisitionStage
  debriefAfterAction : AcquisitionStage

record AcquisitionCell : Set where
  constructor acquisition-cell
  field
    stage : AcquisitionStage
    objectRef : String
    currentlyPaid : Bool
    mayCloseDutyClass : Bool
    mayCloseExactTask : Bool
    mayProveCovertDivergence : Bool
    mayProveCovertDivergenceIsFalse :
      mayProveCovertDivergence ≡ false

open AcquisitionCell public

hansardCell : AcquisitionCell
hansardCell =
  acquisition-cell
    correctionAwareHansard
    "FADT transcript ref. 29619 pp. 49-52 plus applicable Chief of Navy correction(s)"
    false true false false refl

protocolCell : AcquisitionCell
protocolCell =
  acquisition-cell
    embeddingProtocol
    "rules/protocols governing embedded RAN personnel during third-party hostilities"
    false true false false refl

watchCell : AcquisitionCell
watchCell =
  acquisition-cell
    watchDutyAssignment
    "watchbill/duty assignment for the three Australian personnel at the time of the engagement"
    false true true false refl

actionLogCell : AcquisitionCell
actionLogCell =
  acquisition-cell
    operationalActionLog
    "same-episode operational action log identifying actual tasks during the torpedo engagement"
    false true true false refl

debriefCell : AcquisitionCell
debriefCell =
  acquisition-cell
    debriefAfterAction
    "Australian or US debrief/after-action record for the embedded personnel"
    false true true false refl

canonicalAcquisitionOrder : List AcquisitionCell
canonicalAcquisitionOrder =
  hansardCell ∷ protocolCell ∷ watchCell ∷ actionLogCell ∷ debriefCell ∷ []

record PaidBoundary : Set where
  constructor paid-boundary
  field
    presencePaid : Bool
    presencePaidIsTrue : presencePaid ≡ true
    governmentNonOffensivePositionPaid : Bool
    governmentNonOffensivePositionPaidIsTrue :
      governmentNonOffensivePositionPaid ≡ true
    notOrderedToBunksPaid : Bool
    notOrderedToBunksPaidIsTrue :
      notOrderedToBunksPaid ≡ true
    embeddingRulesExistencePaid : Bool
    embeddingRulesExistencePaidIsTrue :
      embeddingRulesExistencePaid ≡ true
    parliamentaryTranscriptIdentityPaid : Bool
    parliamentaryTranscriptIdentityPaidIsTrue :
      parliamentaryTranscriptIdentityPaid ≡ true
    laterCorrectionExistencePaid : Bool
    laterCorrectionExistencePaidIsTrue :
      laterCorrectionExistencePaid ≡ true
    exactDutyPaid : Bool
    exactDutyPaidIsFalse : exactDutyPaid ≡ false
    exactProtocolPaid : Bool
    exactProtocolPaidIsFalse : exactProtocolPaid ≡ false
    independentOperationalReconstructionPaid : Bool
    independentOperationalReconstructionPaidIsFalse :
      independentOperationalReconstructionPaid ≡ false

open PaidBoundary public

currentPaidBoundary : PaidBoundary
currentPaidBoundary =
  paid-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

record RemainingMinCut : Set where
  constructor remaining-min-cut
  field
    cheapestUnpaid : AcquisitionCell
    exactTaskProducer1 : AcquisitionCell
    exactTaskProducer2 : AcquisitionCell
    correctionAwarePromotionRequired : Bool
    correctionAwarePromotionRequiredIsTrue :
      correctionAwarePromotionRequired ≡ true
    historicalAnalogyMayFillGap : Bool
    historicalAnalogyMayFillGapIsFalse :
      historicalAnalogyMayFillGap ≡ false
    sovereigntyVerdictProduced : Bool
    sovereigntyVerdictProducedIsFalse :
      sovereigntyVerdictProduced ≡ false

open RemainingMinCut public

currentMinCut : RemainingMinCut
currentMinCut =
  remaining-min-cut
    hansardCell
    watchCell
    actionLogCell
    true refl
    false refl
    false refl

correctionAwareBundle : Hansard.CorrectionAwarePrimaryBundle
correctionAwareBundle = Hansard.canonicalPrimaryBundle

publicRecordCeiling : Public.PublicRecordCeiling
publicRecordCeiling = Public.canonicalPublicRecordCeiling

currentOpacity : NonAnalogy.CurrentOpacityWitness
currentOpacity = NonAnalogy.irisOpacityWitness

sovereigntyBoundary : Sovereignty.AUKUSCommandSovereigntyBoundary
sovereigntyBoundary = Sovereignty.canonicalBoundary

commandResidual : Command.OperationalResidual
commandResidual = Command.exactDutyResidual

data HansardAloneClosesExactTask : Set where
data ProtocolAloneClosesActualTask : Set where
data OperationalOpacityCreatesHistoricalAnalogy : Set where
data RegulatoryBoundaryCreatesSovereigntyVerdict : Set where

hansardDoesNotCloseExactTask : HansardAloneClosesExactTask → ⊥
hansardDoesNotCloseExactTask ()

protocolDoesNotCloseActualTask : ProtocolAloneClosesActualTask → ⊥
protocolDoesNotCloseActualTask ()

opacityDoesNotCreateHistoricalAnalogy :
  OperationalOpacityCreatesHistoricalAnalogy → ⊥
opacityDoesNotCreateHistoricalAnalogy ()

regulatoryBoundaryDoesNotCreateSovereigntyVerdict :
  RegulatoryBoundaryCreatesSovereigntyVerdict → ⊥
regulatoryBoundaryDoesNotCreateSovereigntyVerdict ()
