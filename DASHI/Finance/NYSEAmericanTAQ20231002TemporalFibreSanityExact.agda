module DASHI.Finance.NYSEAmericanTAQ20231002TemporalFibreSanityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Real-tape sanity specimen from the NYSE American TAQ Trades sample
-- EQY_US_TAQ_AMEX_TRADES_20231002.gz.
--
-- The tape contains, for MNTS:
--   14:26:05.848700631  trade 105 @ 2.44
--   14:26:20.958727265  security status 4 (Trading Halt)
--   14:36:20.959183012  security status 5 (Resume)
--   14:36:27.966617789  trade 105 @ 2.12
--
-- This owner deliberately records only what the tape can establish. It does
-- not promote an observed print size into portfolio-size authority, nor does
-- it infer execution feasibility inside the halted interval from executions
-- observed on either side.
------------------------------------------------------------------------

data MNTSPhase : Set where
  preHaltPhase haltedPhase resumedPhase : MNTSPhase

data TapeEvent : Set where
  preHaltTrade haltStatus resumeStatus postResumeTrade : TapeEvent

sourceTime : TapeEvent → String
sourceTime preHaltTrade = "14:26:05.848700631"
sourceTime haltStatus = "14:26:20.958727265"
sourceTime resumeStatus = "14:36:20.959183012"
sourceTime postResumeTrade = "14:36:27.966617789"

symbol : TapeEvent → String
symbol event = "MNTS"

------------------------------------------------------------------------
-- Trade observations. Prices are represented in integer cents here only for
-- this exact specimen; volume is the actual-share volume printed in Msg 220.
------------------------------------------------------------------------

data IsPrintedTrade : TapeEvent → Set where
  prePrint : IsPrintedTrade preHaltTrade
  postPrint : IsPrintedTrade postResumeTrade

tradePriceCents : (event : TapeEvent) → IsPrintedTrade event → Nat
tradePriceCents preHaltTrade prePrint = 244
tradePriceCents postResumeTrade postPrint = 212

tradeVolumeShares : (event : TapeEvent) → IsPrintedTrade event → Nat
tradeVolumeShares preHaltTrade prePrint = 105
tradeVolumeShares postResumeTrade postPrint = 105

samePrintedVolumeAcrossHalt :
  tradeVolumeShares preHaltTrade prePrint ≡
  tradeVolumeShares postResumeTrade postPrint
samePrintedVolumeAcrossHalt = refl

samePrintedVolumeDoesNotForceSamePrice :
  tradePriceCents preHaltTrade prePrint ≡
  tradePriceCents postResumeTrade postPrint → ⊥
samePrintedVolumeDoesNotForceSamePrice ()

------------------------------------------------------------------------
-- Security-status observations. Msg 34 code 4 is Trading Halt and code 5 is
-- Resume in the NYSE TAQ specification.
------------------------------------------------------------------------

data TapeStatus : MNTSPhase → Set where
  preHaltTrading : TapeStatus preHaltPhase
  tradingHalted : TapeStatus haltedPhase
  tradingResumed : TapeStatus resumedPhase

phaseOf : TapeEvent → MNTSPhase
phaseOf preHaltTrade = preHaltPhase
phaseOf haltStatus = haltedPhase
phaseOf resumeStatus = resumedPhase
phaseOf postResumeTrade = resumedPhase

------------------------------------------------------------------------
-- Execution evidence is proof-relevant and local. The observed prints witness
-- that execution occurred at those exact tape events. There is intentionally
-- no constructor for haltedPhase.
------------------------------------------------------------------------

data TapeExecutionOpen : MNTSPhase → Set where
  preHaltExecutionObserved : TapeExecutionOpen preHaltPhase
  postResumeExecutionObserved : TapeExecutionOpen resumedPhase

haltedExecutionNotOpen : TapeExecutionOpen haltedPhase → ⊥
haltedExecutionNotOpen ()

-- Observing executable states before and after the halt cannot interpolate an
-- execution witness through the halted fibre.
preAndPostExecutionDoNotOpenHalt :
  TapeExecutionOpen preHaltPhase →
  TapeExecutionOpen resumedPhase →
  TapeExecutionOpen haltedPhase → ⊥
preAndPostExecutionDoNotOpenHalt before after halted =
  haltedExecutionNotOpen halted

------------------------------------------------------------------------
-- Tape evidence is not portfolio-transition authority.
------------------------------------------------------------------------

data PortfolioTransition : Set where
  candidate105ShareTransition : PortfolioTransition

observedTapeVolume : PortfolioTransition → Nat
observedTapeVolume candidate105ShareTransition = 105

-- The equality of a candidate's nominal volume with a printed trade volume is
-- merely a numeric collision. It does not construct any of the missing
-- portfolio-level preconditions (PIT universe, inventory, neutrality, risk,
-- turnover, costs/impact, authority, or joint compatibility).

data TapeVolumeEqualsPortfolioAdmissibility : Set where

sameVolumeCannotPromoteToPortfolioAdmissibility :
  TapeVolumeEqualsPortfolioAdmissibility → ⊥
sameVolumeCannotPromoteToPortfolioAdmissibility ()

record NYSEAmericanTAQSanityBoundary : Set where
  constructor nyseAmericanTAQSanityBoundary
  field
    samePrintedSizeImpliesSameTransition : Bool
    samePrintedSizeImpliesSameTransitionIsFalse :
      samePrintedSizeImpliesSameTransition ≡ false

    executionCanBeInterpolatedAcrossHalt : Bool
    executionCanBeInterpolatedAcrossHaltIsFalse :
      executionCanBeInterpolatedAcrossHalt ≡ false

    tapeVolumeCreatesPortfolioSizeAuthority : Bool
    tapeVolumeCreatesPortfolioSizeAuthorityIsFalse :
      tapeVolumeCreatesPortfolioSizeAuthority ≡ false

    tapeEvidenceIsTimeLocal : Bool
    tapeEvidenceIsTimeLocalIsTrue : tapeEvidenceIsTimeLocal ≡ true

canonicalNYSEAmericanTAQSanityBoundary : NYSEAmericanTAQSanityBoundary
canonicalNYSEAmericanTAQSanityBoundary =
  nyseAmericanTAQSanityBoundary false refl false refl false refl true refl

boundaryStatement : String
boundaryStatement =
  "The MNTS 2023-10-02 NYSE American TAQ tape has equal 105-share prints on opposite sides of a Trading Halt/Resume sequence, at different prices. Tape execution evidence is local to its exact phase: it cannot be interpolated through the halted fibre, and matching a printed share count never promotes that number into portfolio-size or joint-admissibility authority."
