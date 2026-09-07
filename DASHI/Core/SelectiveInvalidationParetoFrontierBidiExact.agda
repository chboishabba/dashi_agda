module DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact as Truth
import DASHI.Core.DependencyWeightedDiagnosisSchedulerBidiExact as Weighted

------------------------------------------------------------------------
-- SELECTIVE INVALIDATION + N-DIMENSIONAL / RECURSIVE PARETO BRIDGE
--
-- Compatibility bridge to the methodology of open PR #770:
--   * arbitrary declared semantic axes, not a fixed scalar objective;
--   * residual-relevant materialisation only;
--   * inherited coordinates keep their meaning/cost;
--   * very large / self-indexed ambient capacity does not force brute-force
--     materialisation.
--
-- This file deliberately does NOT duplicate #770's canonical module paths while
-- that PR remains open.  It gives the truth-maintenance API a compatible local
-- frontier surface that can later be collapsed onto RecursiveParetoFrontier-
-- LiftingExact once that owner is on the shared ancestry.
------------------------------------------------------------------------

data RecomputeClass : Set where
  mustRecompute mayRecompute provablyUnaffected authorityBlocked : RecomputeClass

record CertificateCandidate : Set where
  constructor certificate-candidate
  field
    name : String
    diagnosis : Outcome.OutcomeDiagnosis
    class : RecomputeClass
    consequenceCost : Nat
    diagnosticResidualCost : Nat
    authorityPenalty : Nat
    recomputeCost : Nat
    candidateReference : String

open CertificateCandidate public

data FrontierAxis : Set where
  consequenceAxis diagnosticAxis authorityAxis recomputeCostAxis : FrontierAxis

axisCost : FrontierAxis → CertificateCandidate → Nat
axisCost consequenceAxis candidate = consequenceCost candidate
axisCost diagnosticAxis candidate = diagnosticResidualCost candidate
axisCost authorityAxis candidate = authorityPenalty candidate
axisCost recomputeCostAxis candidate = recomputeCost candidate

WeaklyDominates : CertificateCandidate → CertificateCandidate → Set
WeaklyDominates left right =
  (axis : FrontierAxis) → axisCost axis left ≤ axisCost axis right

record ParetoFrontierCandidate (candidate : CertificateCandidate) : Set₁ where
  constructor pareto-frontier-candidate
  field
    residualRelevant : Set
    residualRelevantReceipt : residualRelevant
    authorityAdmissible : authorityPenalty candidate ≡ 0
    frontierReference : String

open ParetoFrontierCandidate public

------------------------------------------------------------------------
-- Tetrational/self-indexed ambient capacity is represented only as capacity
-- metadata.  Materialisation is a separate, consumer/residual-indexed family.
------------------------------------------------------------------------

record AmbientAxisCapacity : Set where
  constructor ambient-axis-capacity
  field
    level : Nat
    capacity : Nat
    recurrenceReference : String
    mayGrowSelfIndexed : Bool

open AmbientAxisCapacity public

record ResidualMaterialisation (ambient : AmbientAxisCapacity) : Set₁ where
  constructor residual-materialisation
  field
    MaterialisedAxis : Set
    includeAxis : MaterialisedAxis → FrontierAxis
    residualRelevant : MaterialisedAxis → Set
    materialisationReference : MaterialisedAxis → String
    consumerReference : String

open ResidualMaterialisation public

canonicalAmbientCapacity : AmbientAxisCapacity
canonicalAmbientCapacity =
  ambient-axis-capacity 3 19683
    "finite calibration only: 3^9 visualisation scale; compatible with #770 self-indexed/tetrational capacity semantics"
    true

data LocalAxis : Set where
  localConsequence localDiagnostic localAuthority localCost : LocalAxis

canonicalResidualMaterialisation : ResidualMaterialisation canonicalAmbientCapacity
canonicalResidualMaterialisation =
  residual-materialisation
    LocalAxis
    include
    (λ axis → ⊤)
    ref
    "current incremental diagnosis recompute consumer"
  where
    include : LocalAxis → FrontierAxis
    include localConsequence = consequenceAxis
    include localDiagnostic = diagnosticAxis
    include localAuthority = authorityAxis
    include localCost = recomputeCostAxis

    ref : LocalAxis → String
    ref localConsequence = "materialise consequence only because affected consumer is live"
    ref localDiagnostic = "materialise diagnostic residual only because diagnosis is live"
    ref localAuthority = "materialise authority gate separately"
    ref localCost = "materialise recompute cost for current frontier choice"

------------------------------------------------------------------------
-- Exact selective-invalidation fixture.
------------------------------------------------------------------------

modelBranch : CertificateCandidate
modelBranch =
  certificate-candidate
    "model branch"
    Outcome.modelConflict
    mustRecompute
    0 0 0 2
    "changed observation -> model -> consumer frontier"

frameBranch : CertificateCandidate
frameBranch =
  certificate-candidate
    "independent frame certificate"
    Outcome.frameConflict
    provablyUnaffected
    4 4 0 0
    "independent frame -> consumer certificate retained by incremental fixture"

consumerReview : CertificateCandidate
consumerReview =
  certificate-candidate
    "consumer reformulation review"
    Outcome.consumerMismatch
    mayRecompute
    2 1 0 1
    "consumer review is live only if the changed branch alters answer adequacy"

authorityReview : CertificateCandidate
authorityReview =
  certificate-candidate
    "authority boundary"
    Outcome.authorityMismatch
    authorityBlocked
    0 0 9 1
    "authority cannot be manufactured by epistemic recomputation"

modelFrontierCandidate : ParetoFrontierCandidate modelBranch
modelFrontierCandidate =
  pareto-frontier-candidate ⊤ tt refl
    "must-recompute changed branch is admitted on current residual frontier"

consumerFrontierCandidate : ParetoFrontierCandidate consumerReview
consumerFrontierCandidate =
  pareto-frontier-candidate ⊤ tt refl
    "may-recompute consumer branch remains Pareto-comparable, not automatically scheduled"

------------------------------------------------------------------------
-- Classification is not preference.  A must-recompute branch may still expose
-- several internal repair/debug candidates; Pareto axes rank those without
-- collapsing consequence, diagnostic reduction, authority, and cost.
------------------------------------------------------------------------

frameDebugger : CertificateCandidate
frameDebugger =
  certificate-candidate
    "frame debugger"
    Outcome.frameConflict
    mayRecompute
    1 0 0 1
    "small control removes a high-consequence framing residual"

largeRepeatDebugger : CertificateCandidate
largeRepeatDebugger =
  certificate-candidate
    "large repeat debugger"
    Outcome.observationConflict
    mayRecompute
    3 6 0 8
    "large repeat remains diagnostically expensive/inert relative to small control"

frameDebuggerDominatesLargeRepeat : WeaklyDominates frameDebugger largeRepeatDebugger
frameDebuggerDominatesLargeRepeat consequenceAxis = s≤s z≤n
frameDebuggerDominatesLargeRepeat diagnosticAxis = z≤n
frameDebuggerDominatesLargeRepeat authorityAxis = z≤n
frameDebuggerDominatesLargeRepeat recomputeCostAxis = s≤s z≤n

------------------------------------------------------------------------
-- Truth-maintenance donor pins.
------------------------------------------------------------------------

incrementalModelFrontierRetained : Truth.RecomputeFrontier Truth.Depends Outcome.modelConflict
incrementalModelFrontierRetained = Truth.modelFrontier

unrelatedFrameCertificateRetained : Truth.FrameCertificate
unrelatedFrameCertificateRetained = Truth.frameCertificateAfterModelRecompute

weightedDiagnosisPriorityStillSeparate : Weighted.DependencyWeightedDiagnosisBoundary
weightedDiagnosisPriorityStillSeparate = Weighted.canonicalDependencyWeightedDiagnosisBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AmbientCapacityForcesMaterialisation : Set where
data ParetoPreferenceMeansMustRecompute : Set where
data ProvablyUnaffectedMeansDeleted : Set where
data AuthorityBlockedMeansLowPriorityEvidence : Set where
data RecomputeClassIsTruthValue : Set where

data TetrationalCapacityMeansTetrationalRuntime : Set where

ambientCapacityDoesNotForceMaterialisation : AmbientCapacityForcesMaterialisation → ⊥
ambientCapacityDoesNotForceMaterialisation ()

paretoPreferenceDoesNotCreateRecomputeObligation : ParetoPreferenceMeansMustRecompute → ⊥
paretoPreferenceDoesNotCreateRecomputeObligation ()

unaffectedCertificateIsRetainedNotDeleted : ProvablyUnaffectedMeansDeleted → ⊥
unaffectedCertificateIsRetainedNotDeleted ()

authorityBlockedIsNotEvidenceRanking : AuthorityBlockedMeansLowPriorityEvidence → ⊥
authorityBlockedIsNotEvidenceRanking ()

recomputeClassIsNotTruthValue : RecomputeClassIsTruthValue → ⊥
recomputeClassIsNotTruthValue ()

tetrationalCapacityDoesNotImplyRuntime : TetrationalCapacityMeansTetrationalRuntime → ⊥
tetrationalCapacityDoesNotImplyRuntime ()

record SelectiveInvalidationParetoBoundary : Set where
  constructor selective-invalidation-pareto-boundary
  field
    classificationSeparateFromParetoRanking : Bool
    fourSemanticAxesRemainDistinct : Bool
    residualMaterialisationMayBeStrictSubsetOfAmbient : Bool
    selfIndexedCapacityMayRemainUnmaterialised : Bool
    provablyUnaffectedCertificateMayBeRetained : Bool
    authorityBlockedNeedsSeparateAuthorityProducer : Bool
    paretoPreferenceCreatesTruthOrAuthority : Bool
    tetrationalCapacityRequiresTetrationalSearch : Bool

canonicalSelectiveInvalidationParetoBoundary : SelectiveInvalidationParetoBoundary
canonicalSelectiveInvalidationParetoBoundary =
  selective-invalidation-pareto-boundary
    true true true true true true false false
