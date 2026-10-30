{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooGasSecondThirdOrderNonPromotion20261030Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Lobby
import DASHI.Law.SensibLawSpringfieldResidentialGasEndpointLockInExact as Endpoint
import DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact as Demand
import DASHI.Law.SensibLawWoogarooEPBC8575PortalClockManifestationExact as Portal

-- A source-listed contact is not a record of the contact's subject matter.
-- Two possible worlds agree about the public diary but disagree about gas tasking.
data LobbyWorld : Set where
  diaryContactNoGasTasking : LobbyWorld
  diaryContactWithGasTasking : LobbyWorld

data DiaryObservation : Set where
  contactRecorded : DiaryObservation

data GasAgenda : Set where
  gasSubjectUnestablished : GasAgenda
  gasSubjectDocumented : GasAgenda

diary : LobbyWorld → DiaryObservation
diary diaryContactNoGasTasking = contactRecorded
diary diaryContactWithGasTasking = contactRecorded

agenda : LobbyWorld → GasAgenda
agenda diaryContactNoGasTasking = gasSubjectUnestablished
agenda diaryContactWithGasTasking = gasSubjectDocumented

distinctAgenda :
  agenda diaryContactNoGasTasking ≡ agenda diaryContactWithGasTasking → ⊥
distinctAgenda ()

diaryCannotDetermineGasAgenda :
  INF.FactorsThrough diary agenda → ⊥
diaryCannotDetermineGasAgenda =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness diaryContactNoGasTasking
      diaryContactWithGasTasking refl distinctAgenda)

-- A gas-connected dwelling does not determine a third-order asset beneficiary.
data EndpointWorld : Set where
  connectionWithoutPaidAssetChain : EndpointWorld
  connectionWithPaidAssetChain : EndpointWorld

data ConnectionObservation : Set where
  connectionPresent : ConnectionObservation

data BeneficiaryEvidence : Set where
  ownerAndRevenueUnpaid : BeneficiaryEvidence
  ownerAndRevenueDocumented : BeneficiaryEvidence

connection : EndpointWorld → ConnectionObservation
connection connectionWithoutPaidAssetChain = connectionPresent
connection connectionWithPaidAssetChain = connectionPresent

beneficiary : EndpointWorld → BeneficiaryEvidence
beneficiary connectionWithoutPaidAssetChain = ownerAndRevenueUnpaid
beneficiary connectionWithPaidAssetChain = ownerAndRevenueDocumented

distinctBeneficiary :
  beneficiary connectionWithoutPaidAssetChain ≡
  beneficiary connectionWithPaidAssetChain → ⊥
distinctBeneficiary ()

connectionCannotDetermineBeneficiary :
  INF.FactorsThrough connection beneficiary → ⊥
connectionCannotDetermineBeneficiary =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness connectionWithoutPaidAssetChain
      connectionWithPaidAssetChain refl distinctBeneficiary)

-- Both worlds show the same federal approval portal status. Neither that
-- status nor adjacent gas relationships decide EPBC project-specific breach.
data ApprovalWorld : Set where
  approvedNoEstablishedBreach : ApprovalWorld
  approvedWithSeparateBreachFinding : ApprovalWorld

data ApprovalObservation : Set where
  approvalPublished : ApprovalObservation

data BreachEvidence : Set where
  breachUnestablished : BreachEvidence
  breachDetermined : BreachEvidence

approval : ApprovalWorld → ApprovalObservation
approval approvedNoEstablishedBreach = approvalPublished
approval approvedWithSeparateBreachFinding = approvalPublished

breach : ApprovalWorld → BreachEvidence
breach approvedNoEstablishedBreach = breachUnestablished
breach approvedWithSeparateBreachFinding = breachDetermined

distinctBreach :
  breach approvedNoEstablishedBreach ≡
  breach approvedWithSeparateBreachFinding → ⊥
distinctBreach ()

approvalCannotDetermineBreach :
  INF.FactorsThrough approval breach → ⊥
approvalCannotDetermineBreach =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness approvedNoEstablishedBreach
      approvedWithSeparateBreachFinding refl distinctBreach)

-- Existing owners imported deliberately; no source is duplicated and no
-- observation, donation, party proximity or gas contact becomes causal proof.
-- The same-object EPBC 2019/8575 approval instrument remains a separate
-- documentary acquisition obligation; Scenic EPBC 2020/8651 is not imported.

// A lobbyist's reported contact and the authority's retained contact record
// are different documentary producers. Even agreement on attendance does not
// determine the content of the request or its downstream disposition.
data ContactWorld : Set where
  matchingRecordsNoPolicyRequest : ContactWorld
  matchingRecordsWithPolicyRequest : ContactWorld

data CorroboratedContact : Set where
  independentlyRecordedAttendance : CorroboratedContact

data RequestContent : Set where
  noGasRequestAuthenticated : RequestContent
  gasRequestAuthenticated : RequestContent

corroboration : ContactWorld → CorroboratedContact
corroboration matchingRecordsNoPolicyRequest = independentlyRecordedAttendance
corroboration matchingRecordsWithPolicyRequest = independentlyRecordedAttendance

requestContent : ContactWorld → RequestContent
requestContent matchingRecordsNoPolicyRequest = noGasRequestAuthenticated
requestContent matchingRecordsWithPolicyRequest = gasRequestAuthenticated

differentContent :
  requestContent matchingRecordsNoPolicyRequest ≡
  requestContent matchingRecordsWithPolicyRequest → ⊥
differentContent ()

corroboratedAttendanceDoesNotDetermineGasRequest :
  INF.FactorsThrough corroboration requestContent → ⊥
corroboratedAttendanceDoesNotDetermineGasRequest =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness matchingRecordsNoPolicyRequest
      matchingRecordsWithPolicyRequest refl differentContent)
