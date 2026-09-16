module DASHI.Finance.TrumpTariffOptionsTimingEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source

------------------------------------------------------------------------
-- INDEPENDENT MARKET-TIMING EVIDENCE
--
-- Source:
-- Reuters, "Well-timed options trades ahead of Trump's tariff pause draw
-- questions", 10 April 2025, no DOI.
--
-- Reuters reported unusually well-timed SPY options trades placed before the
-- April 9 tariff-pause announcement and potential profits in the millions, but
-- also reported that high volatility/volume made wrongdoing difficult to infer.
-- This module therefore pays a market-timing observation while leaving trader
-- identity, information source and legal character unresolved.
------------------------------------------------------------------------

reutersOptionsArtifact : Source.SourceArtifact
reutersOptionsArtifact =
  Source.sourceArtifact
    "Reuters-2025-04-10-SPY-options-timing"
    Source.derivedArtifact
    "https://www.reuters.com/business/finance/well-timed-options-trades-ahead-trumps-tariff-pause-draw-questions-2025-04-10/"
    "Reuters"

record AnonymousTimingEvidence : Set where
  constructor anonymous-timing-evidence
  field
    instrumentReference : String
    tradeTimingReference : String
    outcomeReference : String
    source : Source.SourceArtifact
    sourceTitle : String
    tradeEventObserved : Bool
    traderIdentityPaid : Bool
    TrumpFamilyIdentityPaid : Bool
    privateInformationPaid : Bool
    insiderTradingFindingPaid : Bool

open AnonymousTimingEvidence public

april9SPYOptions : AnonymousTimingEvidence
april9SPYOptions =
  anonymous-timing-evidence
    "SPDR S&P 500 ETF Trust (SPY) options described by Reuters"
    "Reuters reported large bullish options positions, including trades placed shortly before the 1:18 PM tariff-pause announcement"
    "Reuters estimated that some positions could have produced multi-million-dollar gains after the rally"
    reutersOptionsArtifact
    "Well-timed options trades ahead of Trump's tariff pause draw questions"
    true false false false false

------------------------------------------------------------------------
-- This is the evidentiary collision we want: event/timing can be paid while
-- identity and information provenance remain unresolved.
------------------------------------------------------------------------

data AnonymousTradeAutomaticallyBelongsToTrumpFamily : Set where
data TimingPatternAutomaticallyProvesPrivateInformation : Set where
data PotentialProfitAutomaticallyProvesIllegalProfit : Set where

anonymousTradeDoesNotIdentifyTrumpFamily :
  AnonymousTradeAutomaticallyBelongsToTrumpFamily → ⊥
anonymousTradeDoesNotIdentifyTrumpFamily ()

timingPatternDoesNotProvePrivateInformation :
  TimingPatternAutomaticallyProvesPrivateInformation → ⊥
timingPatternDoesNotProvePrivateInformation ()

potentialProfitDoesNotProveIllegality :
  PotentialProfitAutomaticallyProvesIllegalProfit → ⊥
potentialProfitDoesNotProveIllegality ()

record AnonymousTimingBoundary : Set where
  constructor anonymous-timing-boundary
  field
    eventTimingCanBePaidWithoutIdentity : Bool
    identityCanRemainUnresolved : Bool
    privateInformationCanRemainUnresolved : Bool
    investigationCanBeWarrantedWithoutFinding : Bool

canonicalAnonymousTimingBoundary : AnonymousTimingBoundary
canonicalAnonymousTimingBoundary =
  anonymous-timing-boundary true true true true
