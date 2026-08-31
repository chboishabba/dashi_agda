module DASHI.Crypto.TransactionalBraidAssetProvenanceExact where

------------------------------------------------------------------------
-- TRANSACTIONAL BRAID / ASSET PROVENANCE
--
-- Primary interpretation:
--   * asset/entity histories are strands;
--   * transactions/actions are crossings between strands;
--   * an ordered crossing history may preserve a coarse endpoint while changing
--     provenance, attribution, or recoverability of the fine path;
--   * wash/peel-style obfuscation is represented only as an abstract repeated
--     crossing pattern for defensive provenance analysis.
--
-- This owner deliberately does NOT provide a procedure for concealing assets,
-- evading disclosure, laundering value, defeating tracing, or frustrating any
-- legal process.  Pattern recognition does not itself establish unlawful intent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionCrossingBraidExact as Crossing
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Finite asset strands and transaction crossings.
------------------------------------------------------------------------

data AssetStrand : Set where
  originStrand relayStrand sinkStrand : AssetStrand

data TransactionKind : Set where
  transferCrossing
  splitCrossing
  mergeCrossing
  returnCrossing
  : TransactionKind

record TransactionCrossing : Set where
  constructor transaction-crossing
  field
    source : AssetStrand
    target : AssetStrand
    kind : TransactionKind

open TransactionCrossing public

data TransactionTrace : Set where
  directTrace
  washLikeTrace
  peelLikeTrace
  : TransactionTrace

------------------------------------------------------------------------
-- 2. Coarse endpoint can collide while provenance differs.
------------------------------------------------------------------------

data EndpointCode : Set where
  sameTerminalAssetSurface : EndpointCode

data ProvenanceCode : Set where
  directOriginToSink
  returnedThroughRelay
  serialRelayPeel
  : ProvenanceCode

endpoint : TransactionTrace → EndpointCode
endpoint _ = sameTerminalAssetSurface

provenance : TransactionTrace → ProvenanceCode
provenance directTrace = directOriginToSink
provenance washLikeTrace = returnedThroughRelay
provenance peelLikeTrace = serialRelayPeel

sameEndpointDirectWash :
  endpoint directTrace ≡ endpoint washLikeTrace
sameEndpointDirectWash = refl

sameEndpointDirectPeel :
  endpoint directTrace ≡ endpoint peelLikeTrace
sameEndpointDirectPeel = refl

directAndWashProvenanceDiffer :
  provenance directTrace ≡ provenance washLikeTrace → ⊥
directAndWashProvenanceDiffer ()

directAndPeelProvenanceDiffer :
  provenance directTrace ≡ provenance peelLikeTrace → ⊥
directAndPeelProvenanceDiffer ()

transactionActionCrossingSurface : Crossing.ActionCrossingSurface
transactionActionCrossingSurface =
  Crossing.action-crossing-surface
    TransactionTrace
    EndpointCode
    ProvenanceCode
    endpoint
    provenance

canonicalSameEndpointDifferentProvenance :
  Crossing.SameEndpointDifferentProvenance transactionActionCrossingSurface
canonicalSameEndpointDifferentProvenance =
  Crossing.same-endpoint-different-provenance
    directTrace
    washLikeTrace
    refl
    directAndWashProvenanceDiffer

endpointCannotRecoverProvenance :
  INF.FactorsThrough endpoint provenance → ⊥
endpointCannotRecoverProvenance =
  Crossing.endpointCannotRecoverCrossingProvenance
    canonicalSameEndpointDifferentProvenance

------------------------------------------------------------------------
-- 3. Crossing history is first-class, not reconstructed from endpoint alone.
------------------------------------------------------------------------

data CrossingHistoryCode : TransactionTrace → Set where
  directHistory : CrossingHistoryCode directTrace
  washReturnHistory : CrossingHistoryCode washLikeTrace
  peelSerialHistory : CrossingHistoryCode peelLikeTrace

canonicalDirectHistory : CrossingHistoryCode directTrace
canonicalDirectHistory = directHistory

canonicalWashHistory : CrossingHistoryCode washLikeTrace
canonicalWashHistory = washReturnHistory

canonicalPeelHistory : CrossingHistoryCode peelLikeTrace
canonicalPeelHistory = peelSerialHistory

------------------------------------------------------------------------
-- 4. Abstract obfuscation depth: this is a defensive trace-complexity label,
-- not a recipe or guarantee of successful concealment.
------------------------------------------------------------------------

data ProvenanceDepth : Set where
  oneCrossing twoCrossings manyCrossings : ProvenanceDepth

traceDepth : TransactionTrace → ProvenanceDepth
traceDepth directTrace = oneCrossing
traceDepth washLikeTrace = twoCrossings
traceDepth peelLikeTrace = manyCrossings

data ProvenanceDisposition : Set where
  directlyAttributed
  attributionRequiresPathReview
  attributionRequiresSerialPathReview
  : ProvenanceDisposition

provenanceDisposition : TransactionTrace → ProvenanceDisposition
provenanceDisposition directTrace = directlyAttributed
provenanceDisposition washLikeTrace = attributionRequiresPathReview
provenanceDisposition peelLikeTrace = attributionRequiresSerialPathReview

------------------------------------------------------------------------
-- 5. No-promotion / safety boundaries.
------------------------------------------------------------------------

data SameEndpointMeansSameProvenance : Set where

data MoreCrossingsGuaranteeSuccessfulConcealment : Set where

data WashLikePatternProvesIllegalIntent : Set where

data PeelLikePatternProvesIllegalIntent : Set where

data BraidCrossingIsLiteralTopologicalBraidGenerator : Set where

data ProvenanceModelIsLegalConclusion : Set where

data ModelProvidesAssetConcealmentRecipe : Set where

sameEndpointDoesNotMeanSameProvenance : SameEndpointMeansSameProvenance → ⊥
sameEndpointDoesNotMeanSameProvenance ()

moreCrossingsDoNotGuaranteeConcealment :
  MoreCrossingsGuaranteeSuccessfulConcealment → ⊥
moreCrossingsDoNotGuaranteeConcealment ()

washLikePatternDoesNotProveIntent : WashLikePatternProvesIllegalIntent → ⊥
washLikePatternDoesNotProveIntent ()

peelLikePatternDoesNotProveIntent : PeelLikePatternProvesIllegalIntent → ⊥
peelLikePatternDoesNotProveIntent ()

crossingIsNotPromotedToLiteralBraidGenerator :
  BraidCrossingIsLiteralTopologicalBraidGenerator → ⊥
crossingIsNotPromotedToLiteralBraidGenerator ()

provenanceModelDoesNotCreateLegalConclusion : ProvenanceModelIsLegalConclusion → ⊥
provenanceModelDoesNotCreateLegalConclusion ()

modelDoesNotProvideConcealmentRecipe : ModelProvidesAssetConcealmentRecipe → ⊥
modelDoesNotProvideConcealmentRecipe ()

record TransactionalBraidAssetProvenanceBoundary : Set where
  constructor transactional-braid-asset-provenance-boundary
  field
    transactionsRepresentedAsCrossings : Bool
    crossingOrderRetained : Bool
    sameEndpointCanHideDifferentProvenance : Bool
    washAndPeelAreAbstractTracePatterns : Bool
    genericActionCrossingOwnerReused : Bool
    moreCrossingsGuaranteeConcealment : Bool
    patternAloneProvesIntent : Bool
    literalBraidGroupActionConstructed : Bool
    legalConclusionCreated : Bool
    concealmentProcedureProvided : Bool

canonicalTransactionalBraidAssetProvenanceBoundary :
  TransactionalBraidAssetProvenanceBoundary
canonicalTransactionalBraidAssetProvenanceBoundary =
  transactional-braid-asset-provenance-boundary
    true true true true true false false false false false
