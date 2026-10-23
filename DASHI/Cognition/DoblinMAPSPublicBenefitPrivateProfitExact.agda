module DASHI.Cognition.DoblinMAPSPublicBenefitPrivateProfitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DOBLIN / MAPS PUBLIC-BENEFIT <-> PRIVATE-PROFIT ATTRIBUTION OWNER
--
-- Attributed source:
--   Rick Doblin, "The Balance at MAPS Between Public Benefit and Private
--   Profit", Psychedelic Alpha, 23 Jan 2023.
--
-- Independent institutional follow-up:
--   MAPS, "MAPS Welcomes New Investors, Name Change for MAPS Public Benefit
--   Corporation", 5 Jan 2024.
--
-- Doblin's essay strongly pays claims about his stated goals, reasoning and
-- representation of MAPS/MAPS PBC, but is not treated as independent
-- verification of every financial or institutional self-characterisation.
-- The 2024 MAPS release independently pays the later financing/ownership change
-- as an institutional record, while still remaining a MAPS-authored source.
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
  seriesAOver100mClaim : GovernanceClaim
  sharedOwnershipAfterSeriesAClaim : GovernanceClaim
  retainedVotingAndBoardOversightClaim : GovernanceClaim

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

mapsSeriesAReceipt : AttributedGovernanceReceipt
mapsSeriesAReceipt = attributed-governance-receipt
  "Multidisciplinary Association for Psychedelic Studies"
  "MAPS press release"
  "2024-01-05"
  independentInstitutionalRecord
  seriesAOver100mClaim
  true true

mapsSharedOwnershipReceipt : AttributedGovernanceReceipt
mapsSharedOwnershipReceipt = attributed-governance-receipt
  "Multidisciplinary Association for Psychedelic Studies"
  "MAPS press release"
  "2024-01-05"
  independentInstitutionalRecord
  sharedOwnershipAfterSeriesAClaim
  true true

mapsOversightReceipt : AttributedGovernanceReceipt
mapsOversightReceipt = attributed-governance-receipt
  "Multidisciplinary Association for Psychedelic Studies"
  "MAPS press release"
  "2024-01-05"
  independentInstitutionalRecord
  retainedVotingAndBoardOversightClaim
  true true

------------------------------------------------------------------------
-- ATTRIBUTION FIREWALLS.
------------------------------------------------------------------------

data SelfReportIndependentlyVerifiesInstitution : Set where
data PublicBenefitClaimProvesPublicBenefitOutcome : Set where
data MissionStatementNegatesInvestorPressure : Set where
data ForProfitTensionProvesCorruption : Set where
data InstitutionalPressReleaseEqualsExternalAudit : Set where

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

institutionalReleaseDoesNotEqualExternalAudit :
  InstitutionalPressReleaseEqualsExternalAudit → ⊥
institutionalReleaseDoesNotEqualExternalAudit ()

record DoblinMAPSGovernanceBoundary : Set where
  constructor doblin-maps-governance-boundary
  field
    authoredStatementRetainedAsAttribution : Bool
    selfReportEqualsIndependentVerification : Bool
    publicBenefitProfitTensionExplicit : Bool
    publicBenefitClaimEqualsMeasuredOutcome : Bool
    investorPressureMayCoexistWithMission : Bool
    laterSharedOwnershipInstitutionallyRecorded : Bool
    institutionalRecordEqualsExternalAudit : Bool

canonicalDoblinMAPSGovernanceBoundary : DoblinMAPSGovernanceBoundary
canonicalDoblinMAPSGovernanceBoundary =
  doblin-maps-governance-boundary true false true false true true false
