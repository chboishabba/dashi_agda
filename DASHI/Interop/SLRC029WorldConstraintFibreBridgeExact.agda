module DASHI.Interop.SLRC029WorldConstraintFibreBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as World
import DASHI.Interop.SLRSensibLawCandidateWorldAdapterExact as Adapter
import DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact as C029
import DASHI.Policy.ABC730C029IbrahimSourceAtlasExact as Atlas
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Ibrahim

------------------------------------------------------------------------
-- SLR WORLD-CONSTRAINT FIBRE x C029 LEGAL/EVIDENCE CONSUMER
--
-- Runtime companion:
--   tools/slr-discourse-reconstruct/slr_world_constraint_fibre.py
--   schema = slr-world-constraint-fibre-v1
--
-- This bridge does not add a parallel world-model ontology.  It instantiates
-- the generic SLR WorldConstraintFibre with the policy/legal consumer already
-- owned by C029.  Compatibility, consumer adequacy and semantic promotion stay
-- separately typed.
------------------------------------------------------------------------

data ConstraintDimension : Set where
  discourseConstraint : ConstraintDimension
  pnfConstraint : ConstraintDimension
  roleConstraint : ConstraintDimension
  sourceAttributionConstraint : ConstraintDimension
  temporalConstraint : ConstraintDimension
  narrativeConstraint : ConstraintDimension
  authorityConstraint : ConstraintDimension
  legalConsumerConstraint : ConstraintDimension


data ConstraintState : Set where
  paidForCurrentConsumer : ConstraintState
  boundedCandidate : ConstraintState
  residualOpen : ConstraintState
  consumerVeto : ConstraintState

record C029WorldConstraintState : Set where
  constructor c029WorldConstraintState
  field
    discourseState : ConstraintState
    pnfState : ConstraintState
    roleState : ConstraintState
    sourceAttributionState : ConstraintState
    temporalState : ConstraintState
    narrativeState : ConstraintState
    authorityState : ConstraintState
    legalConsumerState : ConstraintState
    currentLegalResidual : C029.C029CutsetResidual
    candidateCompatible : Bool
    consumerAdequate : Bool
    truthPromoted : Bool
    scalarScoreUsed : Bool
    appendOnly : Bool
    runtimeReference : String

open C029WorldConstraintState public

canonicalC029WorldConstraintState : C029WorldConstraintState
canonicalC029WorldConstraintState = c029WorldConstraintState
  boundedCandidate
  boundedCandidate
  boundedCandidate
  paidForCurrentConsumer
  boundedCandidate
  residualOpen
  boundedCandidate
  consumerVeto
  (C029.firstC029Residual C029.canonicalC029Cutset)
  true
  false
  false
  false
  true
  "slr-world-constraint-fibre-v1 -> sl.candidate_world_model.v0_1"

currentLegalResidualIsSettlementClassifier :
  currentLegalResidual canonicalC029WorldConstraintState ≡
  C029.settlementClassifierResidual
currentLegalResidualIsSettlementClassifier =
  C029.currentFirstResidualIsSettlementClassifier

------------------------------------------------------------------------
-- Generic WorldConstraintFibre instance.
--
-- `compatible = true` means the retained candidate is not contradicted by the
-- currently attached world constraints.  It explicitly does NOT mean the C029
-- legal/evidence consumer is adequate or promotion-ready.
------------------------------------------------------------------------

canonicalC029WorldFibre : World.WorldConstraintFibre
canonicalC029WorldFibre = World.worldConstraintFibre
  "SLR CandidateWorldModel discourse span/boundary candidate"
  "PNF residual/topology constraint carried from discourse-quality tables"
  "typed actor/patient/clause/predicate-aux role compatibility"
  "ABC 7.30 same-object primary transcript + source-labelled attribution receipts"
  "ABC source publication date / append-only temporal provenance; event time remains consumer-indexed"
  "Pareto/conflict alternatives retained until source/review contraction"
  "claim-relative primaryness + Ibrahim source coordinates + C029 legal consumer cutset"
  "C029 first residual = settlement-place origin classifier; later advice/incidence/counterfactual residuals remain open"
  true
  "unpaid:review/promote/abstain"

canonicalWorldConstrainedC029Candidate : World.WorldConstrainedDiscourseCandidate
canonicalWorldConstrainedC029Candidate = World.worldConstrainedDiscourseCandidate
  "sl.candidate_world_model.v0_1:C029"
  canonicalC029WorldFibre
  true
  false

------------------------------------------------------------------------
-- C029-specific world-model extension receipt.
------------------------------------------------------------------------

record C029WorldExtensionReceipt : Set where
  constructor c029WorldExtensionReceipt
  field
    sourceObjectReference : String
    deweyCoordinateReference : String
    qidCoordinateReference : String
    doiCoordinateReference : String
    sourcePrimarynessReference : String
    legalCutsetReference : String
    extensionContractsResidualFibre : Bool
    extensionRewritesHistoricalSourceState : Bool
    extensionCreatesClaimTruth : Bool
    extensionCreatesAuthority : Bool

open C029WorldExtensionReceipt public

canonicalC029WorldExtensionReceipt : C029WorldExtensionReceipt
canonicalC029WorldExtensionReceipt = c029WorldExtensionReceipt
  "ABC730C029IbrahimSourceAtlasExact + source URL/SHA same-object weld"
  "Dewey retrieval coordinate; not semantic authority"
  "QID external identity coordinate; not proposition truth"
  "DOI/stable-ID source coordinate; DOI absence remains atlas-local when not observed"
  "primaryness is claim-relative"
  "ABC730C029LegalMachineryHyperfabricExact.canonicalC029Cutset"
  true
  false
  false
  false

------------------------------------------------------------------------
-- Review / promote / abstain routing.
------------------------------------------------------------------------

data ReviewDisposition : Set where
  retainCandidate : ReviewDisposition
  abstainForResidual : ReviewDisposition
  rejectByConsumerVeto : ReviewDisposition
  eligibleForSeparatePromotionReview : ReviewDisposition

reviewC029Candidate : C029WorldConstraintState → ReviewDisposition
reviewC029Candidate state with truthPromoted state
... | true = eligibleForSeparatePromotionReview
... | false with consumerAdequate state
...   | true with candidateCompatible state
...     | true = eligibleForSeparatePromotionReview
...     | false = rejectByConsumerVeto
...   | false with candidateCompatible state
...     | true = abstainForResidual
...     | false = rejectByConsumerVeto

currentReviewDisposition :
  reviewC029Candidate canonicalC029WorldConstraintState ≡ abstainForResidual
currentReviewDisposition = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CompatibleWorldFibreMeansConsumerAdequate : Set where
data ConsumerAdequateMeansTruthPromoted : Set where
data PrimaryTranscriptPaysCausalIncidence : Set where
data QidDeweyDoiPaysPolicyTruth : Set where
data SnowballExtensionMayRewriteHistoricalSource : Set where
data WorldConstraintMayCollapseToScalarScore : Set where
data OpenC029CutsetMayEnableEvaluativeAptness : Set where

compatibleDoesNotMeanAdequate : CompatibleWorldFibreMeansConsumerAdequate → ⊥
compatibleDoesNotMeanAdequate ()

adequateDoesNotMeanTruthPromoted : ConsumerAdequateMeansTruthPromoted → ⊥
adequateDoesNotMeanTruthPromoted ()

primaryTranscriptDoesNotPayIncidence : PrimaryTranscriptPaysCausalIncidence → ⊥
primaryTranscriptDoesNotPayIncidence ()

sourceCoordinatesDoNotPayPolicyTruth : QidDeweyDoiPaysPolicyTruth → ⊥
sourceCoordinatesDoNotPayPolicyTruth ()

snowballDoesNotRewriteHistory : SnowballExtensionMayRewriteHistoricalSource → ⊥
snowballDoesNotRewriteHistory ()

worldConstraintIsNotScalarScore : WorldConstraintMayCollapseToScalarScore → ⊥
worldConstraintIsNotScalarScore ()

openCutsetDoesNotEnableAptness : OpenC029CutsetMayEnableEvaluativeAptness → ⊥
openCutsetDoesNotEnableAptness ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

suiteRoadmapAnchor : World.SuiteConvergenceLaw
suiteRoadmapAnchor = World.canonicalSuiteConvergenceLaw

adapterAnchor : Adapter.SLRSensibLawWorldAdapterReceipt
adapterAnchor = Adapter.canonicalSLRSensibLawWorldAdapterReceipt

c029CutsetAnchor : C029.C029LegalEvidenceCutset
c029CutsetAnchor = C029.canonicalC029Cutset

atlasAnchor : Atlas.AtlasBoundary
atlasAnchor = Atlas.canonicalAtlasBoundary

ibrahimAnchor : Ibrahim.SnowballAttributionBoundary
ibrahimAnchor = Ibrahim.canonicalSnowballAttributionBoundary
