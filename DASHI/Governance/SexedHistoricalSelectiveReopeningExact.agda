module DASHI.Governance.SexedHistoricalSelectiveReopeningExact where

------------------------------------------------------------------------
-- SELECTIVE REOPENING AFTER A PRODUCTIVE HISTORICAL JOIN
--
-- A productive join remains historically reopenable, but a new residual does
-- not invalidate every certificate indiscriminately.  This owner reuses the
-- canonical reverse-dependency closure and adaptive selective-reopening kernel:
--
--   J_t -> changed coordinate -> affected closure -> selective reopening
--       -> consumer-indexed re-measurement -> J_(t+1) search.
--
-- The finite dependency graph below is a DASHI construction.  It is not a
-- source claim about Fukuyama, Kojeve, Hegel, Lacan, Irigaray, or any empirical
-- population.  The End-of-History source roles remain bounded by the adjacent
-- source owner and are not used as proof authority for this dependency graph.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Governance.SexedHistoricalDialecticalJoinAdaptiveSearchExact as Search
import DASHI.Governance.SexedHistoricalReopenableSynthesisEndOfHistoryBoundaryExact as Reopen

------------------------------------------------------------------------
-- 1. Typed historical/join artifacts.
------------------------------------------------------------------------

data HistoricalJoinArtifact : Set where
  counterformationResidual
  powerGateCertificate
  localReachabilityCertificate
  affordanceExpansionCertificate
  productiveJoinCertificate
  nextJoinSearchCertificate
  sourceAttributionCertificate
  : HistoricalJoinArtifact

------------------------------------------------------------------------
-- 2. Reverse dependency graph.
--
-- Changing a counterformation residual affects the situated power gate.  That
-- can alter local reachability, which can alter the affordance-expansion claim,
-- which can invalidate the current productive-join receipt for the relevant
-- consumer and therefore reopen the next join search.
--
-- Source attribution is intentionally outside this causal/dependency chain.
------------------------------------------------------------------------

data Depends : HistoricalJoinArtifact → HistoricalJoinArtifact → Set where
  residualAffectsPowerGate :
    Depends counterformationResidual powerGateCertificate
  powerGateAffectsReachability :
    Depends powerGateCertificate localReachabilityCertificate
  reachabilityAffectsExpansion :
    Depends localReachabilityCertificate affordanceExpansionCertificate
  expansionAffectsProductiveJoin :
    Depends affordanceExpansionCertificate productiveJoinCertificate
  productiveJoinAffectsNextSearch :
    Depends productiveJoinCertificate nextJoinSearchCertificate

------------------------------------------------------------------------
-- 3. Direct and transitive reopening obligations.
------------------------------------------------------------------------

powerGateMustReopen :
  Dependency.ReopeningObligation
    Depends counterformationResidual powerGateCertificate
powerGateMustReopen =
  Dependency.oneEdgeCreatesReopeningObligation residualAffectsPowerGate

localReachabilityMustReopen :
  Dependency.ReopeningObligation
    Depends counterformationResidual localReachabilityCertificate
localReachabilityMustReopen =
  Dependency.obligationsCompose
    powerGateMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation powerGateAffectsReachability)

affordanceExpansionMustReopen :
  Dependency.ReopeningObligation
    Depends counterformationResidual affordanceExpansionCertificate
affordanceExpansionMustReopen =
  Dependency.obligationsCompose
    localReachabilityMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation reachabilityAffectsExpansion)

productiveJoinMustReopen :
  Dependency.ReopeningObligation
    Depends counterformationResidual productiveJoinCertificate
productiveJoinMustReopen =
  Dependency.obligationsCompose
    affordanceExpansionMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation expansionAffectsProductiveJoin)

nextJoinSearchMustReopen :
  Dependency.ReopeningObligation
    Depends counterformationResidual nextJoinSearchCertificate
nextJoinSearchMustReopen =
  Dependency.obligationsCompose
    productiveJoinMustReopen
    (Dependency.oneEdgeCreatesReopeningObligation productiveJoinAffectsNextSearch)

------------------------------------------------------------------------
-- 4. Instantiate the canonical adaptive selective-reopening receipt.
------------------------------------------------------------------------

canonicalSelectiveJoinReopening :
  Adaptive.SelectiveCertificateReopening
    HistoricalJoinArtifact Depends counterformationResidual
canonicalSelectiveJoinReopening =
  Adaptive.selectiveCertificateReopening
    nextJoinSearchCertificate
    (Dependency.dependencyPath nextJoinSearchMustReopen)
    "counterformation residual transitively reopens the affected next-join search"

------------------------------------------------------------------------
-- 5. Reopening selects the consumer-relevant next measurement.
--
-- Once the productive-join receipt has become stale, strict affordance
-- expansion is again an open consumer obligation.  The existing adaptive join
-- search therefore selects the option-cone probe rather than restarting every
-- measurement indiscriminately.
------------------------------------------------------------------------

reopenedJoinSearchSelectsAffordanceProbe :
  Search.nextJoinMeasurement
    Search.verifyStrictAffordanceExpansion
    (Search.joinDisposition Search.unresolvedJoin)
  ≡ Search.optionConeProbe
reopenedJoinSearchSelectsAffordanceProbe = refl

------------------------------------------------------------------------
-- 6. Reopening is not refutation and not global invalidation.
------------------------------------------------------------------------

data ReopenedCertificateIsRefuted : Set where

data CounterformationReopensEveryCertificate : Set where

data SourceAttributionChangesBecauseHistoricalResidualChanged : Set where

data SelectiveReopeningGuaranteesProgress : Set where

data SelectiveReopeningEstablishesHistoricalFinality : Set where

reopenedCertificateIsNotAutomaticallyRefuted :
  ReopenedCertificateIsRefuted → ⊥
reopenedCertificateIsNotAutomaticallyRefuted ()

counterformationDoesNotReopenEverythingWithoutDependencyPath :
  CounterformationReopensEveryCertificate → ⊥
counterformationDoesNotReopenEverythingWithoutDependencyPath ()

historicalResidualDoesNotRewriteSourceAttribution :
  SourceAttributionChangesBecauseHistoricalResidualChanged → ⊥
historicalResidualDoesNotRewriteSourceAttribution ()

selectiveReopeningDoesNotGuaranteeProgress :
  SelectiveReopeningGuaranteesProgress → ⊥
selectiveReopeningDoesNotGuaranteeProgress ()

selectiveReopeningDoesNotEstablishHistoricalFinality :
  SelectiveReopeningEstablishesHistoricalFinality → ⊥
selectiveReopeningDoesNotEstablishHistoricalFinality ()

------------------------------------------------------------------------
-- 7. Cross-owner continuity checks.
------------------------------------------------------------------------

productiveJoinStillHasOutgoingHistory :
  Reopen.JoinTransport Reopen.productiveJoinAtT Reopen.counterformationAtNext
productiveJoinStillHasOutgoingHistory = Reopen.canonicalJoinHasOutgoingTransport

historicalFinalityStillNotPromoted :
  Reopen.CurrentJoinAcceptanceImpliesHistoricalFinalityAcceptance → ⊥
historicalFinalityStillNotPromoted =
  Reopen.currentJoinAcceptanceDoesNotPromoteHistoricalFinality

------------------------------------------------------------------------
-- 8. Boundary summary.
------------------------------------------------------------------------

record SelectiveHistoricalReopeningBoundary : Set where
  constructor selective-historical-reopening-boundary
  field
    counterformationCanReopenDependentCertificates : Bool
    reopeningUsesTransitiveDependencyClosure : Bool
    everyCertificateReopensGlobally : Bool
    staleCertificateEqualsRefutation : Bool
    nextMeasurementCanBeConsumerIndexed : Bool
    sourceAttributionIsRewrittenByResidualChange : Bool
    reopeningGuaranteesProgress : Bool
    reopeningEstablishesHistoricalFinality : Bool

canonicalSelectiveHistoricalReopeningBoundary :
  SelectiveHistoricalReopeningBoundary
canonicalSelectiveHistoricalReopeningBoundary =
  selective-historical-reopening-boundary
    true true false false true false false false
