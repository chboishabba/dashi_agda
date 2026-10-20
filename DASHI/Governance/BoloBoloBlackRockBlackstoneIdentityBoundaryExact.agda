module DASHI.Governance.BoloBoloBlackRockBlackstoneIdentityBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BLACKROCK / BLACKSTONE IDENTITY BOUNDARY
--
-- Attribution-safe source distinction.  First-party histories support a
-- historical lineage between the businesses, but historical lineage does not
-- make the current firms one entity or one controller, and participation in a
-- common financing platform does not re-establish common control.
------------------------------------------------------------------------

record FirmHistorySource : Set where
  constructor firm-history-source
  field
    publisher : String
    sourceReference : String
    boundedSupport : String
    doesNotByItselfSupport : String

open FirmHistorySource public

blackRockHistorySource : FirmHistorySource
blackRockHistorySource = firm-history-source
  "BlackRock"
  "BlackRock corporate history / historical company materials"
  "BlackRock traces its founding to 1988; historical BlackRock materials identify the early business as Blackstone Financial Management and the BlackRock name from 1992"
  "current BlackRock/Blackstone entity identity, current common ownership/control, or transfer of one firm's governance evidence to the other"

blackstoneHistoricalSource : FirmHistorySource
blackstoneHistoricalSource = firm-history-source
  "Blackstone / Stephen A. Schwarzman"
  "Blackstone first-party historical account, 2026"
  "a business that began within Blackstone later left the firm and grew into BlackRock"
  "current common control, current institutional identity, or a shared decision-authority structure"

canonicalFirmHistorySources : List FirmHistorySource
canonicalFirmHistorySources = blackRockHistorySource ∷ blackstoneHistoricalSource ∷ []

record BlackRockBlackstoneIdentityBoundary : Set where
  constructor blackrock-blackstone-identity-boundary
  field
    historicalLineageSourcePresent : Bool
    currentSeparateFirmSourcesPresent : Bool
    historicalLineagePaysCurrentEntityIdentity : Bool
    historicalLineagePaysCurrentCommonControl : Bool
    sharedBlackNamePrefixPaysEntityIdentity : Bool
    sharedFinancingPlatformPaysCommonControl : Bool
    sharedInfrastructureSectorPaysCommonDecisionAuthority : Bool
    oneFirmGovernanceEvidenceTransfersToOtherFirm : Bool
    oneFirmCapitalPositionTransfersToOtherFirm : Bool
    historicalSourceEqualsIndependentArchivalProof : Bool

open BlackRockBlackstoneIdentityBoundary public

canonicalBlackRockBlackstoneIdentityBoundary : BlackRockBlackstoneIdentityBoundary
canonicalBlackRockBlackstoneIdentityBoundary =
  blackrock-blackstone-identity-boundary
    true true
    false false false false false false false false
