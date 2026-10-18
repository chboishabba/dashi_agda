module DASHI.Governance.IRISDenaPublicRecordCeilingAndFOIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact as Command
import DASHI.Governance.IRISDenaSenateEstimatesDutyNarrowingExact as Estimates

------------------------------------------------------------------------
-- IRIS DENA: PUBLIC-RECORD CEILING / FOI ACQUISITION
------------------------------------------------------------------------

defenceFOILog : Source.AttributedSource
defenceFOILog = Source.mkNoDOISource
  "Australian Department of Defence"
  "Freedom of information disclosure log"
  "Department of Defence"
  "2026"
  "https://www.defence.gov.au/about/accessing-information/freedom-information-disclosure-log"
  Source.governmentSource
  "primary Defence disclosure surface; current search pass did not reveal an obvious released same-object protocol/action-log record for the March 2026 IRIS Dena incident"
  Source.publicAttribution

record PublicRecordLayer : Set where
  constructor public-record-layer
  field
    sourceRef : String
    claimRef : String
    sourceRole : String
    paid : Bool
    paidIsTrue : paid ≡ true
    reconstructsExactDuty : Bool
    reconstructsExactDutyIsFalse : reconstructsExactDuty ≡ false

open PublicRecordLayer public

pmLayer : PublicRecordLayer
pmLayer =
  public-record-layer
    "IRISDenaAustralianCommandStatementReceiptExact.pmTranscript"
    "three personnel present; government says no offensive participation"
    "primary executive statement"
    true refl false refl

navyLayer : PublicRecordLayer
navyLayer =
  public-record-layer
    "IRISDenaAustralianCommandStatementReceiptExact.navyDefenceTranscript"
    "not ordered to bunks; performed duties under embedding agreement; no offensive engagement"
    "primary command/ministerial statement"
    true refl false refl

parliamentIndexLayer : PublicRecordLayer
parliamentIndexLayer =
  public-record-layer
    "IRISDenaSenateEstimatesDutyNarrowingExact.parliamentCommitteeIndex"
    "3 June 2026 Senate Estimates examined ADF activities on U.S. submarines at proof-Hansard pp. 49-52"
    "primary parliamentary index"
    true refl false refl

secondaryDutyLayer : PublicRecordLayer
secondaryDutyLayer =
  public-record-layer
    "IRISDenaSenateEstimatesDutyNarrowingExact.liberalPartySummary"
    "secondary summary attributes defensive and platform-maintenance duties to Defence leadership"
    "partisan secondary summary of parliamentary evidence"
    true refl false refl

record PublicRecordCeiling : Set where
  constructor public-record-ceiling
  field
    layers : List PublicRecordLayer
    presencePaid : Bool
    presencePaidIsTrue : presencePaid ≡ true
    nonOffensiveGovernmentPositionPaid : Bool
    nonOffensiveGovernmentPositionPaidIsTrue :
      nonOffensiveGovernmentPositionPaid ≡ true
    dutyClassNarrowingPaid : Bool
    dutyClassNarrowingPaidIsTrue :
      dutyClassNarrowingPaid ≡ true
    dutyClassNarrowingPrimaryVerified : Bool
    dutyClassNarrowingPrimaryVerifiedIsFalse :
      dutyClassNarrowingPrimaryVerified ≡ false
    exactWatchstationPaid : Bool
    exactWatchstationPaidIsFalse :
      exactWatchstationPaid ≡ false
    exactProtocolPaid : Bool
    exactProtocolPaidIsFalse :
      exactProtocolPaid ≡ false
    exactActionLogPaid : Bool
    exactActionLogPaidIsFalse :
      exactActionLogPaid ≡ false

open PublicRecordCeiling public

canonicalPublicRecordCeiling : PublicRecordCeiling
canonicalPublicRecordCeiling =
  public-record-ceiling
    (pmLayer ∷ navyLayer ∷ parliamentIndexLayer ∷ secondaryDutyLayer ∷ [])
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

data AcquisitionObject : Set where
  proofHansardPages49to52 : AcquisitionObject
  embeddingProtocolText : AcquisitionObject
  watchDutyRecord : AcquisitionObject
  operationalActionLog : AcquisitionObject
  debriefOrAfterActionRecord : AcquisitionObject

record FOIAcquisitionDemand : Set where
  constructor foi-acquisition-demand
  field
    object : AcquisitionObject
    targetAgency : String
    sameObjectRequirement : String
    publicDisclosureAlreadyFound : Bool
    publicDisclosureAlreadyFoundIsFalse :
      publicDisclosureAlreadyFound ≡ false
    maySubstituteNewsSummary : Bool
    maySubstituteNewsSummaryIsFalse :
      maySubstituteNewsSummary ≡ false

open FOIAcquisitionDemand public

proofHansardDemand : FOIAcquisitionDemand
proofHansardDemand =
  foi-acquisition-demand
    proofHansardPages49to52
    "Australian Parliament / Senate FADT Legislation Committee"
    "proof Committee Hansard, 3 June 2026, pp. 49-52"
    false refl
    false refl

embeddingProtocolDemand : FOIAcquisitionDemand
embeddingProtocolDemand =
  foi-acquisition-demand
    embeddingProtocolText
    "Australian Department of Defence"
    "rules/protocols governing embedded RAN submariners aboard U.S. Navy SSNs during third-party hostilities"
    false refl
    false refl

watchDutyDemand : FOIAcquisitionDemand
watchDutyDemand =
  foi-acquisition-demand
    watchDutyRecord
    "Australian Department of Defence / U.S. Navy"
    "watchbill/duty assignment for the three Australian personnel at the time of the IRIS Dena engagement"
    false refl
    false refl

actionLogDemand : FOIAcquisitionDemand
actionLogDemand =
  foi-acquisition-demand
    operationalActionLog
    "Australian Department of Defence / U.S. Navy"
    "same-episode action log or equivalent record identifying actual tasks during the torpedo engagement"
    false refl
    false refl

canonicalFOITargets : List FOIAcquisitionDemand
canonicalFOITargets =
  proofHansardDemand
  ∷ embeddingProtocolDemand
  ∷ watchDutyDemand
  ∷ actionLogDemand
  ∷ []

data PublicRecordCeilingMeansNoFurtherRecordExists : Set where
data SecondaryDutySummaryMayBecomePrimary : Set where
data DefensiveDutyMeansNoOperationalContribution : Set where
data NoPublicReleaseMeansNoUnderlyingRecord : Set where

publicCeilingDoesNotProveNoFurtherRecord :
  PublicRecordCeilingMeansNoFurtherRecordExists → ⊥
publicCeilingDoesNotProveNoFurtherRecord ()

secondarySummaryDoesNotPromotePrimary :
  SecondaryDutySummaryMayBecomePrimary → ⊥
secondarySummaryDoesNotPromotePrimary ()

defensiveDutyDoesNotEraseOperationalContribution :
  DefensiveDutyMeansNoOperationalContribution → ⊥
defensiveDutyDoesNotEraseOperationalContribution ()

absenceOfReleaseDoesNotProveAbsenceOfRecord :
  NoPublicReleaseMeansNoUnderlyingRecord → ⊥
absenceOfReleaseDoesNotProveAbsenceOfRecord ()

foiSnowball : Snowball.SourceRoleSnowballReceipt defenceFOILog
foiSnowball = Snowball.canonicalSourceRoleSnowballReceipt defenceFOILog

existingCommandResidual : Command.OperationalResidual
existingCommandResidual = Command.exactDutyResidual

estimatesResidual : Estimates.PrimaryTranscriptResidual
estimatesResidual = Estimates.proofHansardResidual
