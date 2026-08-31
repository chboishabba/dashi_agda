module DASHI.Core.CrossDomainActionBraidCrossPollinationExact where

------------------------------------------------------------------------
-- CROSS-DOMAIN ACTION-BRAID CALIBRATION
--
-- One structural grammar, several distinct semantics:
--   crypto/assets      : transfer/split/merge/return actions;
--   governance         : delegation/veto/institutional action;
--   proof search       : lemma/branch/merge action;
--   markets            : hedge/rebalance/close action;
--   ecology / LES      : repair/disturbance/management action.
--
-- The common theorem is only:
--   same coarse endpoint need not determine ordered action provenance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionCrossingBraidExact as Generic
import DASHI.Core.ActionCrossingTraceCalculusExact as Trace

------------------------------------------------------------------------
-- 1. Domain-indexed scenario traces.
------------------------------------------------------------------------

data Domain : Set where
  cryptoDomain governanceDomain proofDomain marketDomain ecologyDomain : Domain

data Scenario : Domain → Set where
  directAssetPath washLikeAssetPath : Scenario cryptoDomain
  delegateThenVeto vetoThenDelegate : Scenario governanceDomain
  lemmaThenBranch branchThenLemma : Scenario proofDomain
  hedgeThenRebalance rebalanceThenHedge : Scenario marketDomain
  repairThenDisturb disturbThenRepair : Scenario ecologyDomain

data EndpointCode : Domain → Set where
  sameTerminalAsset : EndpointCode cryptoDomain
  sameInstitutionalSurface : EndpointCode governanceDomain
  sameProofGoalSurface : EndpointCode proofDomain
  sameExposureSurface : EndpointCode marketDomain
  sameCurrentSuitability : EndpointCode ecologyDomain

data ProvenanceCode : Domain → Set where
  directAssetProvenance washRelayProvenance : ProvenanceCode cryptoDomain
  delegationFirstProvenance vetoFirstProvenance : ProvenanceCode governanceDomain
  lemmaFirstProvenance branchFirstProvenance : ProvenanceCode proofDomain
  hedgeFirstProvenance rebalanceFirstProvenance : ProvenanceCode marketDomain
  repairFirstProvenance disturbanceFirstProvenance : ProvenanceCode ecologyDomain

endpoint : ∀ {d} → Scenario d → EndpointCode d
endpoint {cryptoDomain} _ = sameTerminalAsset
endpoint {governanceDomain} _ = sameInstitutionalSurface
endpoint {proofDomain} _ = sameProofGoalSurface
endpoint {marketDomain} _ = sameExposureSurface
endpoint {ecologyDomain} _ = sameCurrentSuitability

provenance : ∀ {d} → Scenario d → ProvenanceCode d
provenance directAssetPath = directAssetProvenance
provenance washLikeAssetPath = washRelayProvenance
provenance delegateThenVeto = delegationFirstProvenance
provenance vetoThenDelegate = vetoFirstProvenance
provenance lemmaThenBranch = lemmaFirstProvenance
provenance branchThenLemma = branchFirstProvenance
provenance hedgeThenRebalance = hedgeFirstProvenance
provenance rebalanceThenHedge = rebalanceFirstProvenance
provenance repairThenDisturb = repairFirstProvenance
provenance disturbThenRepair = disturbanceFirstProvenance

------------------------------------------------------------------------
-- 2. Each domain exhibits endpoint collision with provenance separation.
------------------------------------------------------------------------

cryptoSameEndpoint : endpoint directAssetPath ≡ endpoint washLikeAssetPath
cryptoSameEndpoint = refl

cryptoProvenanceDiffers :
  provenance directAssetPath ≡ provenance washLikeAssetPath → ⊥
cryptoProvenanceDiffers ()

governanceSameEndpoint : endpoint delegateThenVeto ≡ endpoint vetoThenDelegate
governanceSameEndpoint = refl

governanceProvenanceDiffers :
  provenance delegateThenVeto ≡ provenance vetoThenDelegate → ⊥
governanceProvenanceDiffers ()

proofSameEndpoint : endpoint lemmaThenBranch ≡ endpoint branchThenLemma
proofSameEndpoint = refl

proofProvenanceDiffers :
  provenance lemmaThenBranch ≡ provenance branchThenLemma → ⊥
proofProvenanceDiffers ()

marketSameEndpoint : endpoint hedgeThenRebalance ≡ endpoint rebalanceThenHedge
marketSameEndpoint = refl

marketProvenanceDiffers :
  provenance hedgeThenRebalance ≡ provenance rebalanceThenHedge → ⊥
marketProvenanceDiffers ()

ecologySameEndpoint : endpoint repairThenDisturb ≡ endpoint disturbThenRepair
ecologySameEndpoint = refl

ecologyProvenanceDiffers :
  provenance repairThenDisturb ≡ provenance disturbThenRepair → ⊥
ecologyProvenanceDiffers ()

------------------------------------------------------------------------
-- 3. Domain-neutral surfaces reuse the canonical non-factorability theorem.
------------------------------------------------------------------------

cryptoSurface : Generic.ActionCrossingSurface
cryptoSurface = Generic.action-crossing-surface
  (Scenario cryptoDomain) (EndpointCode cryptoDomain) (ProvenanceCode cryptoDomain)
  endpoint provenance

cryptoWitness : Generic.SameEndpointDifferentProvenance cryptoSurface
cryptoWitness = Generic.same-endpoint-different-provenance
  directAssetPath washLikeAssetPath refl cryptoProvenanceDiffers

cryptoEndpointCannotRecoverProvenance :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    (Generic.endpoint cryptoSurface) (Generic.provenance cryptoSurface) → ⊥
cryptoEndpointCannotRecoverProvenance =
  Generic.endpointCannotRecoverCrossingProvenance cryptoWitness

------------------------------------------------------------------------
-- 4. Explicit crossing-event vocabulary shared across the domains.
------------------------------------------------------------------------

data CrossDomainStrand : Set where
  assetA assetB institutionA institutionB proofStateA proofStateB
  positionA positionB ecosystemA ecosystemB : CrossDomainStrand

data CrossDomainAction : Set where
  transferAction delegationAction vetoAction lemmaAction branchAction
  hedgeAction rebalanceAction repairAction disturbanceAction : CrossDomainAction

canonicalTransferCrossing : Trace.CrossingEvent CrossDomainStrand CrossDomainAction
canonicalTransferCrossing = Trace.crossing-event assetA assetB transferAction

canonicalDelegationCrossing : Trace.CrossingEvent CrossDomainStrand CrossDomainAction
canonicalDelegationCrossing = Trace.crossing-event institutionA institutionB delegationAction

canonicalProofCrossing : Trace.CrossingEvent CrossDomainStrand CrossDomainAction
canonicalProofCrossing = Trace.crossing-event proofStateA proofStateB lemmaAction

canonicalMarketCrossing : Trace.CrossingEvent CrossDomainStrand CrossDomainAction
canonicalMarketCrossing = Trace.crossing-event positionA positionB hedgeAction

canonicalEcologyCrossing : Trace.CrossingEvent CrossDomainStrand CrossDomainAction
canonicalEcologyCrossing = Trace.crossing-event ecosystemA ecosystemB repairAction

------------------------------------------------------------------------
-- 5. Boundaries.
------------------------------------------------------------------------

data CrossDomainGrammarMeansDomainEquivalence : Set where

data SameEndpointMeansSameCause : Set where

data MoreCrossingsMeansMoreWrongdoing : Set where

data CrossingPatternProvesIntent : Set where

data ProofSearchActionIsFinancialTransaction : Set where

data EcologicalActionIsAssetTransfer : Set where

crossDomainGrammarDoesNotMeanDomainEquivalence :
  CrossDomainGrammarMeansDomainEquivalence → ⊥
crossDomainGrammarDoesNotMeanDomainEquivalence ()

sameEndpointDoesNotMeanSameCause : SameEndpointMeansSameCause → ⊥
sameEndpointDoesNotMeanSameCause ()

moreCrossingsDoNotMeanMoreWrongdoing : MoreCrossingsMeansMoreWrongdoing → ⊥
moreCrossingsDoNotMeanMoreWrongdoing ()

crossingPatternDoesNotProveIntent : CrossingPatternProvesIntent → ⊥
crossingPatternDoesNotProveIntent ()

proofSearchActionIsNotFinancialTransaction : ProofSearchActionIsFinancialTransaction → ⊥
proofSearchActionIsNotFinancialTransaction ()

ecologicalActionIsNotAssetTransfer : EcologicalActionIsAssetTransfer → ⊥
ecologicalActionIsNotAssetTransfer ()

record CrossDomainActionBraidBoundary : Set where
  constructor cross-domain-action-braid-boundary
  field
    oneCrossingGrammarShared : Bool
    cryptoEndpointCollisionOwned : Bool
    governanceEndpointCollisionOwned : Bool
    proofEndpointCollisionOwned : Bool
    marketEndpointCollisionOwned : Bool
    ecologyEndpointCollisionOwned : Bool
    domainsDeclaredEquivalent : Bool
    crossingPatternProvesIntent : Bool
    crossingCountDeterminesWrongdoing : Bool

canonicalCrossDomainActionBraidBoundary : CrossDomainActionBraidBoundary
canonicalCrossDomainActionBraidBoundary =
  cross-domain-action-braid-boundary true true true true true true false false false
