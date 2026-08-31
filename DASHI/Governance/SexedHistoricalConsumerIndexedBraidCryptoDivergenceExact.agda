module DASHI.Governance.SexedHistoricalConsumerIndexedBraidCryptoDivergenceExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED DIVERGENCE / BRAID / CRYPTO-OBSERVATION BRIDGE
--
-- The same pair of fine histories need not have one universal divergence
-- depth.  Divergence is relative to the declared consumer/observation language:
--
--   * immediate-action consumer: histories remain equivalent;
--   * long-horizon consumer: first visible divergence is at long horizon;
--   * braid-provenance consumer: ordered mediation trace already separates.
--
-- Cross-pollinations are structural only:
--   * defensive crypto observation-language refinement supplies the exact
--     base-observation + extra-coordinate split grammar;
--   * market-control abstention supplies HOLD != FLAT / neutral != close;
--   * QFT braiding receipt supplies a hard non-promotion boundary: the current
--     finite physical braid surface does not construct non-abelian intertwiners.
--
-- No cryptocurrency market mechanism, side-channel leak, braid-group action,
-- Yang-Baxter solution, or economic prediction is asserted by this owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Control.LearnedAbstentionBoundary as Market
import DASHI.Crypto.AttackerObservationLanguageRefinementExact as CryptoObs
import DASHI.Physics.QFT.BraidingMorphismReceipt as QFTBraid
import DASHI.Governance.SexedHistoricalStratifiedFutureConeQuotientExact as Future
import DASHI.Governance.SexedHistoricalHorizonFiltrationFirstDivergenceExact as Horizon
import DASHI.Governance.SexedHistoricalHorizonQualifiedSelectiveReopeningExact as Reopen

data HistoricalConsumer : Set where
  immediateActionConsumer
  shortForecastConsumer
  mediumForecastConsumer
  longForecastConsumer
  braidProvenanceConsumer
  riskControlConsumer
  : HistoricalConsumer

data ConsumerDivergenceCode : Set where
  noDivergenceWithinDeclaredScope
  firstVisibleAtLongHorizon
  braidTraceAlreadySeparates
  independentRiskDirectiveRequired
  : ConsumerDivergenceCode

consumerDivergence : HistoricalConsumer → ConsumerDivergenceCode
consumerDivergence immediateActionConsumer = noDivergenceWithinDeclaredScope
consumerDivergence shortForecastConsumer = noDivergenceWithinDeclaredScope
consumerDivergence mediumForecastConsumer = noDivergenceWithinDeclaredScope
consumerDivergence longForecastConsumer = firstVisibleAtLongHorizon
consumerDivergence braidProvenanceConsumer = braidTraceAlreadySeparates
consumerDivergence riskControlConsumer = independentRiskDirectiveRequired

immediateAndLongConsumersDiffer :
  consumerDivergence immediateActionConsumer
  ≡ consumerDivergence longForecastConsumer → ⊥
immediateAndLongConsumersDiffer ()

longAndBraidConsumersDiffer :
  consumerDivergence longForecastConsumer
  ≡ consumerDivergence braidProvenanceConsumer → ⊥
longAndBraidConsumersDiffer ()

data BraidTrace : Set where
  pluralisationBeforeInstitutionalClosure
  institutionalClosureBeforePluralisation
  : BraidTrace

braidTrace : Future.FuturePathHistory → BraidTrace
braidTrace Future.repairedThenPluralised = pluralisationBeforeInstitutionalClosure
braidTrace Future.repairedThenInstitutionalised = institutionalClosureBeforePluralisation

braidTracesDiffer :
  braidTrace Future.repairedThenPluralised
  ≡ braidTrace Future.repairedThenInstitutionalised → ⊥
braidTracesDiffer ()

historicalBraidObservationLanguage : CryptoObs.ObservationLanguage
historicalBraidObservationLanguage =
  CryptoObs.observationLanguage
    Future.FuturePathHistory
    Future.ImmediateChoice
    BraidTrace
    Future.immediateChoice
    braidTrace

immediateActionBaseEquivalent :
  CryptoObs.BaseEquivalent
    historicalBraidObservationLanguage
    Future.repairedThenPluralised
    Future.repairedThenInstitutionalised
immediateActionBaseEquivalent = refl

historicalBraidLanguageSplit :
  CryptoObs.LanguageSplitWitness historicalBraidObservationLanguage
historicalBraidLanguageSplit =
  CryptoObs.languageSplitWitness
    Future.repairedThenPluralised
    Future.repairedThenInstitutionalised
    refl
    braidTracesDiffer

braidProvenanceRefinesImmediateActionLanguage :
  CryptoObs.ExtendedEquivalent
    historicalBraidObservationLanguage
    Future.repairedThenPluralised
    Future.repairedThenInstitutionalised → ⊥
braidProvenanceRefinesImmediateActionLanguage =
  CryptoObs.splitRefutesExtendedEquivalence historicalBraidLanguageSplit

shortForecastStillAgrees :
  Horizon.coneAt Horizon.shortHorizon Future.repairedThenPluralised
  ≡ Horizon.coneAt Horizon.shortHorizon Future.repairedThenInstitutionalised
shortForecastStillAgrees = Horizon.shortHorizonAgreement

mediumForecastStillAgrees :
  Horizon.coneAt Horizon.mediumHorizon Future.repairedThenPluralised
  ≡ Horizon.coneAt Horizon.mediumHorizon Future.repairedThenInstitutionalised
mediumForecastStillAgrees = Horizon.mediumHorizonAgreement

longForecastFirstDivergence : Horizon.FirstForecastDivergenceAt Horizon.longHorizon
longForecastFirstDivergence = Horizon.canonicalFirstForecastDivergence

data ConsumerPairRelation : HistoricalConsumer → Set where
  immediatePairEquivalent : ConsumerPairRelation immediateActionConsumer
  shortPairEquivalent : ConsumerPairRelation shortForecastConsumer
  mediumPairEquivalent : ConsumerPairRelation mediumForecastConsumer
  longPairSeparated : ConsumerPairRelation longForecastConsumer
  braidPairSeparated : ConsumerPairRelation braidProvenanceConsumer
  riskPairNeedsIndependentDirective : ConsumerPairRelation riskControlConsumer

canonicalImmediateRelation : ConsumerPairRelation immediateActionConsumer
canonicalImmediateRelation = immediatePairEquivalent

canonicalLongRelation : ConsumerPairRelation longForecastConsumer
canonicalLongRelation = longPairSeparated

canonicalBraidRelation : ConsumerPairRelation braidProvenanceConsumer
canonicalBraidRelation = braidPairSeparated

marketNeutralDoesNotFlattenPrecedent :
  Market.compileDecision (Market.decision Market.neutral false) ≡ Market.hold
marketNeutralDoesNotFlattenPrecedent = Market.neutralDoesNotFlatten

marketAbstentionPreservesHoldPrecedent :
  Market.compileDecision (Market.decision Market.up true) ≡ Market.hold
marketAbstentionPreservesHoldPrecedent = Market.abstentionCompilesToHold Market.up

marketRiskCloseIsExplicitPrecedent :
  Market.compileRisk Market.closeExposure Market.hold ≡ Market.flatten
marketRiskCloseIsExplicitPrecedent = Market.onlyRiskClosesExposure Market.hold

historicalImmediateActionStillRetained :
  Reopen.RetainedBelowFirstDivergence Reopen.immediateActionCertificate
historicalImmediateActionStillRetained = Reopen.canonicalImmediateRetention

qftFiniteSurfaceDoesNotConstructNonAbelianIntertwiners :
  QFTBraid.nonAbelianBraidingIntertwinerConstructed
    QFTBraid.canonicalBraidingMorphismReceipt
  ≡ false
qftFiniteSurfaceDoesNotConstructNonAbelianIntertwiners =
  QFTBraid.finitePrimeLaneBraidingDoesNotConstructNonAbelianIntertwiners

data ConsumerIndexedDivergenceIsUniversalMetric : Set where

data BraidTraceIsCryptographicSideChannel : Set where

data HistoricalBraidIsNonAbelianBraidGroupAction : Set where

data HistoricalBraidSatisfiesYangBaxter : Set where

data SameImmediateActionErasesBraidProvenance : Set where

data NeutralHistoricalDispositionMeansFlattenAllOptions : Set where

data CryptoObservationAnalogyProvesCryptocurrencyMechanism : Set where

data BraidConsumerHasUniversalAuthority : Set where

data ProvenanceSeparationRefutesImmediateAction : Set where

consumerIndexedDivergenceIsNotUniversalMetric : ConsumerIndexedDivergenceIsUniversalMetric → ⊥
consumerIndexedDivergenceIsNotUniversalMetric ()

braidTraceIsNotCryptographicSideChannel : BraidTraceIsCryptographicSideChannel → ⊥
braidTraceIsNotCryptographicSideChannel ()

historicalBraidIsNotNonAbelianBraidGroupAction : HistoricalBraidIsNonAbelianBraidGroupAction → ⊥
historicalBraidIsNotNonAbelianBraidGroupAction ()

historicalBraidDoesNotEstablishYangBaxter : HistoricalBraidSatisfiesYangBaxter → ⊥
historicalBraidDoesNotEstablishYangBaxter ()

sameImmediateActionDoesNotEraseBraidProvenance : SameImmediateActionErasesBraidProvenance → ⊥
sameImmediateActionDoesNotEraseBraidProvenance ()

neutralDoesNotMeanFlattenAllOptions : NeutralHistoricalDispositionMeansFlattenAllOptions → ⊥
neutralDoesNotMeanFlattenAllOptions ()

cryptoObservationAnalogyDoesNotProveCryptocurrencyMechanism :
  CryptoObservationAnalogyProvesCryptocurrencyMechanism → ⊥
cryptoObservationAnalogyDoesNotProveCryptocurrencyMechanism ()

braidConsumerDoesNotHaveUniversalAuthority : BraidConsumerHasUniversalAuthority → ⊥
braidConsumerDoesNotHaveUniversalAuthority ()

provenanceSeparationDoesNotRefuteImmediateAction : ProvenanceSeparationRefutesImmediateAction → ⊥
provenanceSeparationDoesNotRefuteImmediateAction ()

record ConsumerIndexedBraidCryptoDivergenceBoundary : Set where
  constructor consumer-indexed-braid-crypto-divergence-boundary
  field
    immediateConsumerKeepsPairEquivalent : Bool
    longConsumerFirstSeparatesAtLongHorizon : Bool
    braidProvenanceConsumerSeparatesEarlier : Bool
    cryptoObservationLanguageRefinementReused : Bool
    neutralDoesNotFlatten : Bool
    explicitRiskDirectiveRequiredForFlatten : Bool
    historicalBraidIsNonAbelianAction : Bool
    cryptoAnalogyEstablishesCryptocurrencyMechanism : Bool
    consumerDivergenceIsUniversalMetric : Bool

canonicalConsumerIndexedBraidCryptoDivergenceBoundary :
  ConsumerIndexedBraidCryptoDivergenceBoundary
canonicalConsumerIndexedBraidCryptoDivergenceBoundary =
  consumer-indexed-braid-crypto-divergence-boundary
    true true true true true true false false false
