module DASHI.Cognition.PNF.SensibLawGriffithsCustodialOutcomePaymentV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousCustodianshipDutyCrossPollinationExact as Custody
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- GRIFFITHS / TIMBER CREEK CONSUMER-SPECIFIC COMMUNITY OUTCOME PAYMENT V02
--
-- This is intentionally narrow.  It does not claim to define satisfactory
-- justice for all First Nations, all Traditional Owners, or all Country claims.
-- It uses the already-owned Griffiths accepted-evidence receipt only for the
-- custodial relation it actually supports: responsibility/concern to look after
-- Country and the experienced failure of that responsibility when Country is
-- harmed.
------------------------------------------------------------------------

data CustodialConsumer : Set where
  timberCreekCustodialRelationConsumer : CustodialConsumer

data CustodialOutcome : Set where
  enableFulfilmentOfLookAfterCountryResponsibility : CustodialOutcome

record ConsumerMatchedCustodialOutcomeV02 : Set where
  constructor consumer-matched-custodial-outcome-v02
  field
    consumer : CustodialConsumer
    outcome : CustodialOutcome
    sourceReceipt : Custody.CustodialDutyReceipt
    sourceAuthorityIsIndigenousLawAndCustom :
      Custody.authorityKind sourceReceipt ≡ Custody.indigenousLawAndCustomAuthority
    sourceObligationIsTraditionalCustodialResponsibility :
      Custody.obligationKind sourceReceipt
      ≡ Custody.indigenousTraditionalLawCustodialResponsibility
    sourceRolePreserved : Custody.sourceRolePreserved sourceReceipt ≡ true
    sourcePropositionReference : String
    consumerMatchReference : String
    outcomeDerivationReference : String
    currentRepresentationalMandatePaid : Bool
    currentRepresentationalMandatePaidIsFalse :
      currentRepresentationalMandatePaid ≡ false
    specificInstitutionalRemedyPaid : Bool
    specificInstitutionalRemedyPaidIsFalse : specificInstitutionalRemedyPaid ≡ false

open ConsumerMatchedCustodialOutcomeV02 public

griffithsCustodialOutcomePayment : ConsumerMatchedCustodialOutcomeV02
griffithsCustodialOutcomePayment = consumer-matched-custodial-outcome-v02
  timberCreekCustodialRelationConsumer
  enableFulfilmentOfLookAfterCountryResponsibility
  Custody.griffithsTraditionalCustodialDuty
  refl
  refl
  refl
  "accepted evidence: duty/concern to look after Country and sense of failed responsibility under traditional laws/customs when Country was harmed"
  "consumer is exactly the custodial-relation coordinate evidenced in Griffiths, not a universal Indigenous-justice consumer"
  "DASHI operational restatement: for this narrowly declared custodial consumer, a satisfactory state must permit rather than frustrate fulfilment of the evidenced responsibility to look after Country; no particular legal remedy is inferred"
  false refl
  false refl

------------------------------------------------------------------------
-- This pays the outcome coordinate only for the narrow custodial consumer.
-- Authority/mandate for a present representative and the institutional
-- correction capable of realising the outcome remain separate residuals.
------------------------------------------------------------------------

griffithsOutcomeDeltaV02 : Assessment.SearchFrontierDelta
griffithsOutcomeDeltaV02 = Assessment.searchFrontierDelta
  "Timber Creek custodial-relation consumer"
  "affected-community outcome unresolved for this narrow custodial relation"
  "consumer-matched custodial outcome admitted from Griffiths accepted evidence"
  Assessment.frontierClosed
  "affectedCommunityOutcomeResidualV02"
  "communityAuthorityCapacityResidualV02"
  "accepted evidence identifies traditional-law custodial responsibility; operational payment is limited to the same custodial consumer"
  "griffiths-timber-creek/custodial-outcome-payment/v02"

griffithsOutcomeAdvancesToAuthorityResidual :
  Assessment.firstResidualAfterReference griffithsOutcomeDeltaV02
  ≡ "communityAuthorityCapacityResidualV02"
griffithsOutcomeAdvancesToAuthorityResidual = refl

currentMandateStillOpen :
  currentRepresentationalMandatePaid griffithsCustodialOutcomePayment ≡ false
currentMandateStillOpen = refl

specificInstitutionalRemedyStillOpen :
  specificInstitutionalRemedyPaid griffithsCustodialOutcomePayment ≡ false
specificInstitutionalRemedyStillOpen = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GriffithsCustodialOutcomePaysAllCountryConsumers : Set where
data TraditionalDutySelectsSpecificStateRemedy : Set where
data HistoricalAcceptedEvidenceCreatesCurrentRepresentativeMandate : Set where

griffithsOutcomeDoesNotPayAllCountryConsumers :
  GriffithsCustodialOutcomePaysAllCountryConsumers → ⊥
griffithsOutcomeDoesNotPayAllCountryConsumers ()

traditionalDutyDoesNotSelectSpecificStateRemedy :
  TraditionalDutySelectsSpecificStateRemedy → ⊥
traditionalDutyDoesNotSelectSpecificStateRemedy ()

historicalEvidenceDoesNotCreateCurrentMandate :
  HistoricalAcceptedEvidenceCreatesCurrentRepresentativeMandate → ⊥
historicalEvidenceDoesNotCreateCurrentMandate ()

record GriffithsCustodialOutcomeBoundary : Set where
  constructor griffiths-custodial-outcome-boundary
  field
    narrowConsumerOutcomePaid : Bool
    narrowConsumerOutcomePaidIsTrue : narrowConsumerOutcomePaid ≡ true
    wholeCommunityMandatePaid : Bool
    wholeCommunityMandatePaidIsFalse : wholeCommunityMandatePaid ≡ false
    specificInstitutionalCorrectionPaid : Bool
    specificInstitutionalCorrectionPaidIsFalse : specificInstitutionalCorrectionPaid ≡ false
    outcomePaymentAdvancesToAuthorityResidual : Bool
    outcomePaymentAdvancesToAuthorityResidualIsTrue :
      outcomePaymentAdvancesToAuthorityResidual ≡ true

open GriffithsCustodialOutcomeBoundary public

canonicalGriffithsCustodialOutcomeBoundary : GriffithsCustodialOutcomeBoundary
canonicalGriffithsCustodialOutcomeBoundary = griffiths-custodial-outcome-boundary
  true refl
  false refl
  false refl
  true refl

bridgeStillTreatsCommunityAuthorityAsSeparateResidual :
  Bridge.communityAuthorityStatusIsStructuralConstraintMapped
  ≡ Bridge.communityAuthorityStatusIsStructuralConstraintMapped
bridgeStillTreatsCommunityAuthorityAsSeparateResidual = refl
