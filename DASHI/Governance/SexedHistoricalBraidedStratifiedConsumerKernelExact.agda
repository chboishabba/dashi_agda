module DASHI.Governance.SexedHistoricalBraidedStratifiedConsumerKernelExact where

------------------------------------------------------------------------
-- BRAIDED STRATIFIED CONSUMER KERNEL
--
-- A "consumer kernel" here is only an observational-kernel analogy:
-- a local strand swap is kernel-safe for consumer C when C cannot distinguish
-- the before/after ordered braid histories.  No group representation, normal
-- subgroup, Yang-Baxter relation, or algebraic kernel theorem is claimed.
--
-- This owner cross-pollinates:
--   * ordered fibre-braid transport;
--   * Base369 centre/face/edge/corner consumer stratification;
--   * consumer-indexed horizon divergence;
--   * revolutionary-practice distinct-strand / unity-not-uniformity boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.FibreBraidReasoning as FibreBraid
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.RevolutionaryPracticeBraid as PracticeBraid
import DASHI.Governance.SexedHistoricalConsumerIndexedBraidCryptoDivergenceExact as Consumer
import DASHI.Governance.SexedHistoricalStratifiedMultiConsumerClosureExact as Multi

------------------------------------------------------------------------
-- 1. Historical strands and finite ordered braid words.
------------------------------------------------------------------------

data HistoricalStrand : Set where
  evidenceStrand
  fidelityStrand
  supportStrand
  institutionalStrand
  relationalStrand
  ecologicalStrand
  : HistoricalStrand

data BraidWord2 : Set where
  braidWord : HistoricalStrand → HistoricalStrand → BraidWord2

swap2 : BraidWord2 → BraidWord2
swap2 (braidWord left right) = braidWord right left

------------------------------------------------------------------------
-- 2. Consumer observations of two-strand order.
------------------------------------------------------------------------

data ImmediateOrderCode : Set where
  sameImmediateActionCode : ImmediateOrderCode

data ProvenanceOrderCode : Set where
  evidenceBeforeFidelity
  fidelityBeforeEvidence
  supportBeforeInstitution
  institutionBeforeSupport
  otherOrder
  : ProvenanceOrderCode

data FutureOrderCode : Set where
  sameNearFutureCode
  supportFirstLongFuture
  institutionFirstLongFuture
  : FutureOrderCode

immediateOrder : BraidWord2 → ImmediateOrderCode
immediateOrder _ = sameImmediateActionCode

provenanceOrder : BraidWord2 → ProvenanceOrderCode
provenanceOrder (braidWord evidenceStrand fidelityStrand) = evidenceBeforeFidelity
provenanceOrder (braidWord fidelityStrand evidenceStrand) = fidelityBeforeEvidence
provenanceOrder (braidWord supportStrand institutionalStrand) = supportBeforeInstitution
provenanceOrder (braidWord institutionalStrand supportStrand) = institutionBeforeSupport
provenanceOrder _ = otherOrder

futureOrder : BraidWord2 → FutureOrderCode
futureOrder (braidWord supportStrand institutionalStrand) = supportFirstLongFuture
futureOrder (braidWord institutionalStrand supportStrand) = institutionFirstLongFuture
futureOrder _ = sameNearFutureCode

------------------------------------------------------------------------
-- 3. Consumer-relative swap safety.
------------------------------------------------------------------------

record SwapSafeImmediate (word : BraidWord2) : Set where
  constructor swap-safe-immediate
  field
    invisibleToImmediate : immediateOrder word ≡ immediateOrder (swap2 word)

record SwapSafeProvenance (word : BraidWord2) : Set where
  constructor swap-safe-provenance
  field
    invisibleToProvenance : provenanceOrder word ≡ provenanceOrder (swap2 word)

record SwapSafeFuture (word : BraidWord2) : Set where
  constructor swap-safe-future
  field
    invisibleToFuture : futureOrder word ≡ futureOrder (swap2 word)

evidenceFidelityWord : BraidWord2
evidenceFidelityWord = braidWord evidenceStrand fidelityStrand

supportInstitutionWord : BraidWord2
supportInstitutionWord = braidWord supportStrand institutionalStrand

evidenceFidelitySwapImmediateSafe : SwapSafeImmediate evidenceFidelityWord
evidenceFidelitySwapImmediateSafe = swap-safe-immediate refl

evidenceFidelitySwapNotProvenanceSafe :
  SwapSafeProvenance evidenceFidelityWord → ⊥
evidenceFidelitySwapNotProvenanceSafe (swap-safe-provenance ())

supportInstitutionSwapImmediateSafe : SwapSafeImmediate supportInstitutionWord
supportInstitutionSwapImmediateSafe = swap-safe-immediate refl

supportInstitutionSwapNotFutureSafe :
  SwapSafeFuture supportInstitutionWord → ⊥
supportInstitutionSwapNotFutureSafe (swap-safe-future ())

supportInstitutionSwapNotProvenanceSafe :
  SwapSafeProvenance supportInstitutionWord → ⊥
supportInstitutionSwapNotProvenanceSafe (swap-safe-provenance ())

------------------------------------------------------------------------
-- 4. Stratum-index the consumer question without identifying strata with
-- meanings.  These are declared finite placements only.
------------------------------------------------------------------------

consumerKernelStratum : Consumer.HistoricalConsumer → Strata.VoxelStratum
consumerKernelStratum Consumer.immediateActionConsumer = Strata.centreStratum
consumerKernelStratum Consumer.shortForecastConsumer = Strata.faceCentreStratum
consumerKernelStratum Consumer.mediumForecastConsumer = Strata.edgeCentreStratum
consumerKernelStratum Consumer.longForecastConsumer = Strata.cornerStratum
consumerKernelStratum Consumer.braidProvenanceConsumer = Strata.edgeCentreStratum
consumerKernelStratum Consumer.riskControlConsumer = Strata.cornerStratum

immediateKernelLivesAtCentre :
  consumerKernelStratum Consumer.immediateActionConsumer ≡ Strata.centreStratum
immediateKernelLivesAtCentre = refl

longKernelLivesAtCorner :
  consumerKernelStratum Consumer.longForecastConsumer ≡ Strata.cornerStratum
longKernelLivesAtCorner = refl

------------------------------------------------------------------------
-- 5. Continuity with existing braid semantics.
------------------------------------------------------------------------

practiceBraidKeepsStrandsDistinct :
  PracticeBraid.braidRetainsDistinctStrands
    PracticeBraid.canonicalRevolutionaryPracticeBraidSurface
  ≡ true
practiceBraidKeepsStrandsDistinct = refl

practiceBraidUnityDoesNotRequireUniformity :
  PracticeBraid.unityRequiresUniformity
    PracticeBraid.canonicalRevolutionaryPracticeBraidSurface
  ≡ false
practiceBraidUnityDoesNotRequireUniformity = refl

-- The cognition braid precedent explicitly gives ordered sequential transport;
-- associativity of the underlying triXor parenthesisation does not create a
-- theorem that arbitrary strand order is observationally irrelevant.
fibreBraidSingleTransportPrecedent = FibreBraid.singleAuxiliaryTransport

------------------------------------------------------------------------
-- 6. Relationship to existing stratified consumer placement.
------------------------------------------------------------------------

existingGlobalCompatibilityConsumerIsEdge :
  Multi.consumerStratum Multi.globalCompatibilityConsumer
  ≡ Strata.edgeCentreStratum
existingGlobalCompatibilityConsumerIsEdge = refl

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data ConsumerKernelIsAlgebraicKernel : Set where

data SwapSafeForOneConsumerMeansSwapSafeForAll : Set where

data ImmediateSwapSafetyErasesProvenance : Set where

data BraidWordsFormBraidGroupHere : Set where

data YangBaxterRelationConstructedHere : Set where

data StratumDeterminesSwapSafety : Set where

data DistinctStrandsCannotCoordinate : Set where

data KernelSafetyCreatesNormativePermission : Set where

consumerKernelIsNotAlgebraicKernel : ConsumerKernelIsAlgebraicKernel → ⊥
consumerKernelIsNotAlgebraicKernel ()

swapSafetyIsNotUniversalAcrossConsumers :
  SwapSafeForOneConsumerMeansSwapSafeForAll → ⊥
swapSafetyIsNotUniversalAcrossConsumers ()

immediateSwapSafetyDoesNotEraseProvenance :
  ImmediateSwapSafetyErasesProvenance → ⊥
immediateSwapSafetyDoesNotEraseProvenance ()

braidWordsAreNotPromotedToBraidGroup : BraidWordsFormBraidGroupHere → ⊥
braidWordsAreNotPromotedToBraidGroup ()

yangBaxterIsNotConstructedHere : YangBaxterRelationConstructedHere → ⊥
yangBaxterIsNotConstructedHere ()

stratumDoesNotDetermineSwapSafety : StratumDeterminesSwapSafety → ⊥
stratumDoesNotDetermineSwapSafety ()

distinctStrandsCanStillCoordinate : DistinctStrandsCannotCoordinate → ⊥
distinctStrandsCanStillCoordinate ()

kernelSafetyDoesNotCreateNormativePermission :
  KernelSafetyCreatesNormativePermission → ⊥
kernelSafetyDoesNotCreateNormativePermission ()

record BraidedStratifiedConsumerKernelBoundary : Set where
  constructor braided-stratified-consumer-kernel-boundary
  field
    orderedStrandsExplicit : Bool
    immediateConsumerCanIgnoreSomeSwaps : Bool
    provenanceConsumerCanRejectSameSwap : Bool
    futureConsumerCanRejectSupportInstitutionSwap : Bool
    strataIndexConsumers : Bool
    strandsRemainDistinct : Bool
    consumerKernelIsAlgebraicKernel : Bool
    braidGroupConstructed : Bool
    yangBaxterConstructed : Bool
    kernelSafetyCreatesPermission : Bool

canonicalBraidedStratifiedConsumerKernelBoundary :
  BraidedStratifiedConsumerKernelBoundary
canonicalBraidedStratifiedConsumerKernelBoundary =
  braided-stratified-consumer-kernel-boundary
    true true true true true true false false false false
