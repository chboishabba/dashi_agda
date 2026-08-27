module DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact where

------------------------------------------------------------------------
-- TRADING DECLARED / REALIZED VIABILITY BRIDGE
--
-- Cross-pollination target:
--   DASHI.Core.DeclaredRealizedIntegrityResidualExact owns the generic record
--   separating a declared observation from a realized situated observation and
--   their residual.  In the social-ecology specimen this is nominal public
--   access versus realized ability to remain.  Here we reuse only that generic
--   record shape for proposal direction versus realized BUY viability.
--
-- This is a structural reuse, not a semantic identification of markets with
-- social ecology and not a Solis/SCN claim about trading.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

------------------------------------------------------------------------
-- A fixed portfolio/agent role lets the current market/portfolio fabric state
-- play the environment coordinate of the generic situated observer.
------------------------------------------------------------------------

data TradingAgent : Set where
  canonicalTradingAgent : TradingAgent

data ViabilityResidual : Set where
  proposalViabilityAligned proposalViabilityMismatch : ViabilityResidual

proposalObservation : Dream.TradingFabricState → Dream.Direction
proposalObservation = Dream.candidateObserver

realizedBuyViability :
  TradingAgent → Dream.TradingFabricState → Bool
realizedBuyViability canonicalTradingAgent state =
  Dream.actionAvailable state Dream.buyAction

viabilityResidual : Dream.Direction → Bool → ViabilityResidual
viabilityResidual Dream.longDirection true = proposalViabilityAligned
viabilityResidual Dream.longDirection false = proposalViabilityMismatch
viabilityResidual Dream.flatDirection viable = proposalViabilityMismatch
viabilityResidual Dream.shortDirection viable = proposalViabilityMismatch

tradingProposalViabilityObserver :
  Integrity.SituatedIntegrityObserver
    TradingAgent
    Dream.TradingFabricState
    Dream.Direction
    Bool
    ViabilityResidual
tradingProposalViabilityObserver =
  Integrity.situatedIntegrityObserver
    proposalObservation
    realizedBuyViability
    viabilityResidual

cleanLongResidual :
  Integrity.integrityResidual
    tradingProposalViabilityObserver
    canonicalTradingAgent
    Dream.cleanLongState
  ≡ proposalViabilityAligned
cleanLongResidual = refl

crowdedLongResidual :
  Integrity.integrityResidual
    tradingProposalViabilityObserver
    canonicalTradingAgent
    Dream.crowdedLongState
  ≡ proposalViabilityMismatch
crowdedLongResidual = refl

sameProposalDifferentResidual :
  Integrity.integrityResidual
    tradingProposalViabilityObserver
    canonicalTradingAgent
    Dream.cleanLongState
  ≡ Integrity.integrityResidual
      tradingProposalViabilityObserver
      canonicalTradingAgent
      Dream.crowdedLongState →
  ⊥
sameProposalDifferentResidual ()

------------------------------------------------------------------------
-- Proposal-only observation therefore cannot recover the residual either.
------------------------------------------------------------------------

proposalCannotRecoverViabilityResidual :
  NF.NonFactorabilityWitness
    Dream.candidateObserver
    (λ state →
      Integrity.integrityResidual
        tradingProposalViabilityObserver
        canonicalTradingAgent
        state)
proposalCannotRecoverViabilityResidual =
  NF.nonFactorabilityWitness
    Dream.cleanLongState
    Dream.crowdedLongState
    Dream.sameLongProposal
    sameProposalDifferentResidual

noProposalOnlyResidualClassifier :
  NF.FactorsThrough
    Dream.candidateObserver
    (λ state →
      Integrity.integrityResidual
        tradingProposalViabilityObserver
        canonicalTradingAgent
        state) →
  ⊥
noProposalOnlyResidualClassifier =
  NF.witnessRulesOutEveryFlatFactorisation
    proposalCannotRecoverViabilityResidual

postprocessedProposalStillCannotRecoverResidual :
  ∀ {Chart : Set} →
  (rechart : Dream.Direction → Chart) →
  NF.FactorsThrough
    (λ state → rechart (Dream.candidateObserver state))
    (λ state →
      Integrity.integrityResidual
        tradingProposalViabilityObserver
        canonicalTradingAgent
        state) →
  ⊥
postprocessedProposalStillCannotRecoverResidual rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart proposalCannotRecoverViabilityResidual

------------------------------------------------------------------------
-- Boundary: theorem-pattern reuse does not transfer domain semantics.
------------------------------------------------------------------------

record TradingDeclaredRealizedBoundary : Set where
  constructor trading-declared-realized-boundary
  field
    proposalDirectionIsAuthorization : Bool
    proposalDirectionIsAuthorizationIsFalse :
      proposalDirectionIsAuthorization ≡ false
    proposalDirectionDeterminesRealizedBuyViability : Bool
    proposalDirectionDeterminesRealizedBuyViabilityIsFalse :
      proposalDirectionDeterminesRealizedBuyViability ≡ false
    socialEcologyAndTradingAreDefinitionallyIdentical : Bool
    socialEcologyAndTradingAreDefinitionallyIdenticalIsFalse :
      socialEcologyAndTradingAreDefinitionallyIdentical ≡ false
    solisSCNAppliesToTradingByThisBridge : Bool
    solisSCNAppliesToTradingByThisBridgeIsFalse :
      solisSCNAppliesToTradingByThisBridge ≡ false
    genericDeclaredRealizedObserverReused : Bool
    genericDeclaredRealizedObserverReusedIsTrue :
      genericDeclaredRealizedObserverReused ≡ true

canonicalTradingDeclaredRealizedBoundary : TradingDeclaredRealizedBoundary
canonicalTradingDeclaredRealizedBoundary =
  trading-declared-realized-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
