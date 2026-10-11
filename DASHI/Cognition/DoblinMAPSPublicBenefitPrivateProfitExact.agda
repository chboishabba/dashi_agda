module DASHI.Cognition.DoblinMAPSPublicBenefitPrivateProfitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DOBLIN / MAPS PUBLIC-BENEFIT <-> PRIVATE-PROFIT ATTRIBUTION OWNER
--
-- Primary attributed source for this owner:
--   Rick Doblin, "The Balance at MAPS Between Public Benefit and Private
--   Profit", Psychedelic Alpha, 23 Jan 2023.
--
-- This is Doblin writing about the organisation he founded.  It strongly pays
-- claims about his stated goals, reasoning and representation of MAPS/MAPS PBC,
-- but is not treated as independent verification of every financial or
-- institutional self-characterisation.
------------------------------------------------------------------------

data AttributionKind : Set where
  authorSelfReport : AttributionKind
  independentInstitutionalRecord : AttributionKind
  independentReporting : AttributionKind

data GovernanceClaim : Set where
  publicBenefitPrivateProfitTension : GovernanceClaim
  mapsPBCWhollyOwnedClaim : GovernanceClaim
  dataExclusivityStrategyClaim : GovernanceClaim
  donorFundedOpenScienceClaim : GovernanceClaim
  revenueShareFinancingClaim : GovernanceClaim
  publicBenefitPriorityClaim : GovernanceClaim

record AttributedGovernanceReceipt : Set where
  constructor attributed-governance-receipt
  field
    author : String
    venue : String
    date : String
    attribution : AttributionKind
    claim : GovernanceClaim
    explicitlyStated : Bool
    independentlyVerifiedHere : Bool
open AttributedGovernanceReceipt public

doblinPublicBenefitProfitReceipt : AttributedGovernanceReceipt
doblinPublicBenefitProfitReceipt = attributed-governance-receipt
  "Rick Doblin"
  "Psychedelic Alpha"
  "2023-01-23"
  authorSelfReport
  publicBenefitPrivateProfitTension
  true false

doblinWhollyOwnedPBCReceipt : AttributedGovernanceReceipt
doblinWhollyOwnedPBCReceipt = attributed-governance-receipt
  "Rick Doblin"
  "Psychedelic Alpha"
  "2023-01-23"
  authorSelfReport
  mapsPBCWhollyOwnedClaim
  true false

doblinDataExclusivityReceipt : AttributedGovernanceReceipt
doblinDataExclusivityReceipt = attributed-governance-receipt
  "Rick Doblin"
  "Psychedelic Alpha"
  "2023-01-23"
  authorSelfReport
  dataExclusivityStrategyClaim
  true false

doblinRevenueShareReceipt : AttributedGovernanceReceipt
doblinRevenueShareReceipt = attributed-governance-receipt
  "Rick Doblin"
  "Psychedelic Alpha"
  "2023-01-23"
  authorSelfReport
  revenueShareFinancingClaim
  true false

------------------------------------------------------------------------
-- ATTRIBUTION FIREWALLS.
------------------------------------------------------------------------

data SelfReportIndependentlyVerifiesInstitution : Set where
data PublicBenefitClaimProvesPublicBenefitOutcome : Set where
data MissionStatementNegatesInvestorPressure : Set where
data ForProfitTensionProvesCorruption : Set where

selfReportDoesNotIndependentlyVerify :
  SelfReportIndependentlyVerifiesInstitution → ⊥
selfReportDoesNotIndependentlyVerify ()

publicBenefitClaimDoesNotProveOutcome :
  PublicBenefitClaimProvesPublicBenefitOutcome → ⊥
publicBenefitClaimDoesNotProveOutcome ()

missionStatementDoesNotNegateInvestorPressure :
  MissionStatementNegatesInvestorPressure → ⊥
missionStatementDoesNotNegateInvestorPressure ()

forProfitTensionDoesNotProveCorruption :
  ForProfitTensionProvesCorruption → ⊥
forProfitTensionDoesNotProveCorruption ()

record DoblinMAPSGovernanceBoundary : Set where
  constructor doblin-maps-governance-boundary
  field
    authoredStatementRetainedAsAttribution : Bool
    selfReportEqualsIndependentVerification : Bool
    publicBenefitProfitTensionExplicit : Bool
    publicBenefitClaimEqualsMeasuredOutcome : Bool
    investorPressureMayCoexistWithMission : Bool

canonicalDoblinMAPSGovernanceBoundary : DoblinMAPSGovernanceBoundary
canonicalDoblinMAPSGovernanceBoundary =
  doblin-maps-governance-boundary true false true false true
