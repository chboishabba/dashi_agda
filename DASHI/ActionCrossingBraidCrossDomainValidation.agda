module DASHI.ActionCrossingBraidCrossDomainValidation where

open import DASHI.Core.Prelude
open import Data.List using (length)

import DASHI.Core.ActionCrossingBraidExact as Generic
import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Core.ActionCrossingConsumerQuotientExact as Consumer
import DASHI.Core.ActionCrossingMotifExact as Motif
import DASHI.Core.CrossDomainActionBraidCrossPollinationExact as Cross
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Crypto.TransactionalBraidAssetProvenanceExact as Crypto
import DASHI.Crypto.TransactionalBraidMotifRecognitionExact as CryptoMotif
import DASHI.Governance.SexedHistoricalActionCrossingInstantiationExact as Historical

traceAssociativityRegression :
  ∀ {Strand Action}
    (left middle right : Trace.ActionTrace Strand Action) →
  Trace._++trace_ (Trace._++trace_ left middle) right
  ≡ Trace._++trace_ left (Trace._++trace_ middle right)
traceAssociativityRegression = Trace.traceConcatenationAssociative

cryptoEndpointCannotRecoverProvenanceRegression :
  INF.FactorsThrough Crypto.endpoint Crypto.provenance → ⊥
cryptoEndpointCannotRecoverProvenanceRegression = Crypto.endpointCannotRecoverProvenance

crossDomainCryptoNonDescentRegression :
  INF.FactorsThrough
    (Generic.endpoint Cross.cryptoSurface)
    (Generic.provenance Cross.cryptoSurface) → ⊥
crossDomainCryptoNonDescentRegression = Cross.cryptoEndpointCannotRecoverProvenance

governanceEndpointCollisionRegression :
  Cross.endpoint Cross.delegateThenVeto ≡ Cross.endpoint Cross.vetoThenDelegate
governanceEndpointCollisionRegression = Cross.governanceSameEndpoint

proofEndpointCollisionRegression :
  Cross.endpoint Cross.lemmaThenBranch ≡ Cross.endpoint Cross.branchThenLemma
proofEndpointCollisionRegression = Cross.proofSameEndpoint

marketEndpointCollisionRegression :
  Cross.endpoint Cross.hedgeThenRebalance ≡ Cross.endpoint Cross.rebalanceThenHedge
marketEndpointCollisionRegression = Cross.marketSameEndpoint

ecologyEndpointCollisionRegression :
  Cross.endpoint Cross.repairThenDisturb ≡ Cross.endpoint Cross.disturbThenRepair
ecologyEndpointCollisionRegression = Cross.ecologySameEndpoint

historicalSameCrossingCountRegression :
  length Historical.supportThenInstitution
  ≡ length Historical.institutionThenSupport
historicalSameCrossingCountRegression = Historical.sameCrossingCountSupportInstitution

historicalEndpointCannotRecoverProvenanceRegression :
  INF.FactorsThrough Historical.coarseEndpoint Historical.historicalProvenance → ⊥
historicalEndpointCannotRecoverProvenanceRegression =
  Historical.endpointCannotRecoverHistoricalProvenance

relayMotifRegression : Motif.RelayMotif Motif.relayTrace
relayMotifRegression = Motif.canonicalRelay

returnCycleMotifRegression : Motif.ReturnCycleMotif Motif.returnTrace
returnCycleMotifRegression = Motif.canonicalReturn

splitMotifRegression : Motif.SplitMotif Motif.splitTrace
splitMotifRegression = Motif.canonicalSplit

crossingCountCannotRecoverMotifRegression :
  INF.FactorsThrough Motif.crossingCount Motif.motifCode → ⊥
crossingCountCannotRecoverMotifRegression = Motif.countCannotRecoverMotif

motifConsumerSplitRegression :
  Consumer.ConsumerSplit
    Motif.countConsumer Motif.motifConsumer Motif.relayReturnRewrite
motifConsumerSplitRegression = Motif.relayReturnConsumerSplit

cryptoWashLikeReturnMotifRegression :
  Motif.ReturnCycleMotif CryptoMotif.washLikeReturnTrace
cryptoWashLikeReturnMotifRegression = CryptoMotif.washLikeReturnMotif

cryptoPeelLikeRelayMotifRegression :
  Motif.RelayMotif CryptoMotif.peelLikeRelayTrace
cryptoPeelLikeRelayMotifRegression = CryptoMotif.peelLikeRelayMotif

actionCrossingTraceBoundaryRegression : Trace.ActionCrossingTraceBoundary
actionCrossingTraceBoundaryRegression = Trace.canonicalActionCrossingTraceBoundary

actionCrossingConsumerBoundaryRegression : Consumer.ActionCrossingConsumerQuotientBoundary
actionCrossingConsumerBoundaryRegression =
  Consumer.canonicalActionCrossingConsumerQuotientBoundary

actionCrossingMotifBoundaryRegression : Motif.ActionCrossingMotifBoundary
actionCrossingMotifBoundaryRegression = Motif.canonicalActionCrossingMotifBoundary

cryptoMotifBoundaryRegression : CryptoMotif.TransactionalBraidMotifRecognitionBoundary
cryptoMotifBoundaryRegression =
  CryptoMotif.canonicalTransactionalBraidMotifRecognitionBoundary

crossDomainActionBraidBoundaryRegression : Cross.CrossDomainActionBraidBoundary
crossDomainActionBraidBoundaryRegression = Cross.canonicalCrossDomainActionBraidBoundary

cryptoTransactionalBraidBoundaryRegression : Crypto.TransactionalBraidAssetProvenanceBoundary
cryptoTransactionalBraidBoundaryRegression =
  Crypto.canonicalTransactionalBraidAssetProvenanceBoundary

historicalActionCrossingBoundaryRegression : Historical.SexedHistoricalActionCrossingBoundary
historicalActionCrossingBoundaryRegression =
  Historical.canonicalSexedHistoricalActionCrossingBoundary
