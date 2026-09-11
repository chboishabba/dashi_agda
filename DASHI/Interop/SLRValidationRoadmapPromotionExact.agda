module DASHI.Interop.SLRValidationRoadmapPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRRuntimeValidationHandoffExact as Validation
import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as Roadmap
import DASHI.Interop.SLRSensibLawCandidateWorldAdapterExact as Adapter
import DASHI.Interop.SLRABCGoldBenchmarkRuntimeContractExact as Gold
import DASHI.Interop.SLRC029WorldConstraintFibreBridgeExact as World
import DASHI.Interop.SLRReviewPromoteAbstainConsumerExact as Review
import DASHI.Interop.SLRClaimFragmentProjectionExact as Fragment
import DASHI.Interop.SLRClaimFragmentResidualInheritanceExact as FragmentResidual

------------------------------------------------------------------------
-- Validation-to-roadmap promotion.
--
-- Runtime validation pays carrier/execution parity. It does not silently pay
-- gold semantic dimensions, world truth, canonical claim truth, or consumer
-- adequacy. Existing owners remain authoritative for those obligations.
------------------------------------------------------------------------

data PromotedRoadmapState : Set where
  paid : PromotedRoadmapState
  partial : PromotedRoadmapState
  active : PromotedRoadmapState
  blockedByMissingSource : PromotedRoadmapState

record PromotedRoadmapCoordinate : Set where
  constructor promotedRoadmapCoordinate
  field
    coordinateReference : String
    state : PromotedRoadmapState
    paymentReference : String
    remainingResidualReference : String

open PromotedRoadmapCoordinate public

currentSLRValidationRoadmap : List PromotedRoadmapCoordinate
currentSLRValidationRoadmap =
  promotedRoadmapCoordinate
    "SLR -> SensibLaw CandidateWorldModel carrier normalization"
    paid
    "SLR_RUNTIME_VALIDATION: ABC730 normalization_drift=false; 405 claims; 53 relations; 76 conflicts; 153 residuals"
    "semantic claim identity and world constraints are separate"
  ∷ promotedRoadmapCoordinate
    "cross-corpus direct/reference execution parity"
    paid
    "GWB 41,134 sentences + AU retained-source 19,235 sentences; parity_failed=0; published=0"
    "does not establish domain semantics"
  ∷ promotedRoadmapCoordinate
    "gold-labelled ABC discourse benchmark"
    partial
    "SLRABCGoldBenchmarkRuntimeContractExact"
    "quote/nesting gold, calibrated uncertainty, aligned residual-fibre delta"
  ∷ promotedRoadmapCoordinate
    "multi-hop labelled discourse path"
    paid
    "validated path artifact: sentence 42 Wong -> Greber -> Husic; sentence 45 Shoebridge -> Leeser"
    "path adjacency does not by itself pay whole-claim source extent"
  ∷ promotedRoadmapCoordinate
    "claim-local fragment projection"
    partial
    "SLRClaimFragmentProjectionExact / slr-claim-fragment-projection-v1"
    "dedicated runtime receipt pending; whole canonical claim extent remains unpaid"
  ∷ promotedRoadmapCoordinate
    "claim-local fragment residual inheritance"
    partial
    "SLRClaimFragmentResidualInheritanceExact / slr-claim-fragment-residual-inheritance-v1"
    "dedicated runtime receipt pending; inherited consumer debt does not promote claim truth"
  ∷ promotedRoadmapCoordinate
    "world-constraint fibre integration"
    partial
    "SLRC029WorldConstraintFibreBridgeExact / slr-world-constraint-fibre-v1"
    "domain/legal consumer adequacy remains open"
  ∷ promotedRoadmapCoordinate
    "review/promote/abstain routing"
    paid
    "SLRReviewPromoteAbstainConsumerExact / slr-review-disposition-v1"
    "current C029 candidate correctly abstains because residual remains open"
  ∷ promotedRoadmapCoordinate
    "canonical claim/evidence projection"
    partial
    "SLRCanonicalClaimProjectionExact / slr-canonical-claim-projection-v2: historical explicit sentence mappings plus same-source unique-phrase/offset exact-subspan refinement"
    "execute v2 projection against tracked ABC primary source; claim truth remains separately unpromoted"
  ∷ promotedRoadmapCoordinate
    "Brexit narrative benchmark"
    blockedByMissingSource
    "structured intent fixture exists"
    "retained narrative/source text not available"
  ∷ []

record ValidationPromotionBoundary : Set where
  constructor validationPromotionBoundary
  field
    carrierParityPaid : Bool
    executionParityPaid : Bool
    reviewRouterImplemented : Bool
    multiHopDiscoursePathPaid : Bool
    goldSemanticBenchmarkFullyPaid : Bool
    worldTruthPaid : Bool
    canonicalClaimProjectionImplemented : Bool
    canonicalClaimProjectionRuntimeCertified : Bool
    claimFragmentProjectionImplemented : Bool
    claimFragmentProjectionRuntimeCertified : Bool
    fragmentResidualInheritanceImplemented : Bool
    fragmentResidualInheritanceRuntimeCertified : Bool
    canonicalClaimTruthPaid : Bool
    brexitNarrativeBenchmarkPaid : Bool

open ValidationPromotionBoundary public

canonicalValidationPromotionBoundary : ValidationPromotionBoundary
canonicalValidationPromotionBoundary =
  validationPromotionBoundary
    true true true true
    false false
    true false
    true false
    true false
    false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RuntimeParityPaysGoldSemantics : Set where
data CarrierParityPaysClaimIdentity : Set where
data ClaimProjectionImplementationPaysRuntimeCertification : Set where
data FragmentProjectionImplementationPaysRuntimeCertification : Set where
data FragmentResidualInheritancePaysRuntimeCertification : Set where
data CanonicalClaimProjectionPaysClaimTruth : Set where
data ReviewRouterImplementationPaysConsumerAdequacy : Set where
data CurrentAbstentionMeansClaimFalse : Set where
data MissingBrexitNarrativeMayBeSynthesisedFromIntentFixture : Set where

runtimeParityDoesNotPayGoldSemantics : RuntimeParityPaysGoldSemantics → ⊥
runtimeParityDoesNotPayGoldSemantics ()

carrierParityDoesNotPayClaimIdentity : CarrierParityPaysClaimIdentity → ⊥
carrierParityDoesNotPayClaimIdentity ()

implementationDoesNotPayProjectionRuntime :
  ClaimProjectionImplementationPaysRuntimeCertification → ⊥
implementationDoesNotPayProjectionRuntime ()

fragmentImplementationDoesNotPayRuntime :
  FragmentProjectionImplementationPaysRuntimeCertification → ⊥
fragmentImplementationDoesNotPayRuntime ()

fragmentResidualImplementationDoesNotPayRuntime :
  FragmentResidualInheritancePaysRuntimeCertification → ⊥
fragmentResidualImplementationDoesNotPayRuntime ()

projectionDoesNotPayClaimTruth : CanonicalClaimProjectionPaysClaimTruth → ⊥
projectionDoesNotPayClaimTruth ()

routerDoesNotPayAdequacy : ReviewRouterImplementationPaysConsumerAdequacy → ⊥
routerDoesNotPayAdequacy ()

abstentionDoesNotMeanFalse : CurrentAbstentionMeansClaimFalse → ⊥
abstentionDoesNotMeanFalse ()

brexitFixtureMayNotManufactureNarrative :
  MissingBrexitNarrativeMayBeSynthesisedFromIntentFixture → ⊥
brexitFixtureMayNotManufactureNarrative ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

validationAnchor : Validation.SLRValidationBoundary
validationAnchor = Validation.canonicalSLRValidationBoundary

suiteAnchor : Roadmap.SuiteConvergenceLaw
suiteAnchor = Roadmap.canonicalSuiteConvergenceLaw

adapterAnchor : Adapter.SLRSensibLawWorldAdapterReceipt
adapterAnchor = Adapter.canonicalSLRSensibLawWorldAdapterReceipt

reviewAnchor : Review.RuntimeReviewContract
reviewAnchor = Review.canonicalRuntimeReviewContract

worldAnchor : World.C029WorldConstraintState
worldAnchor = World.canonicalC029WorldConstraintState

fragmentAnchor : Fragment.ClaimFragmentProjectionBoundary
fragmentAnchor = Fragment.canonicalClaimFragmentProjectionBoundary

fragmentResidualAnchor : FragmentResidual.FragmentResidualRuntimeBoundary
fragmentResidualAnchor = FragmentResidual.canonicalFragmentResidualRuntimeBoundary
