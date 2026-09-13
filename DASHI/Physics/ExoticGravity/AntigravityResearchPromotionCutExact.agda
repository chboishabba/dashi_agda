module DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.AntigravityClaimTheoryComparisonExact as Claim
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- TERMINAL RESEARCH-PROMOTION CUT
--
-- This is intentionally weaker than "antigravity proved".  It says that one
-- exact antigravity claim has survived the declared same-apparatus experimental
-- cut and has an attributed same-scope theory comparison whose ordinary
-- residual is closed and whose alternative residual is smaller under the
-- declared comparison budget.
------------------------------------------------------------------------

record SameApparatusExperimentalCut : Set where
  constructor same-apparatus-experimental-cut
  field
    sourceBundle : Plan.FullSourceGeometryBundleReceipt
    phaseProbeBundle : Plan.PhaseProbeBundleReceipt
    ordinaryModelBundle : Plan.OrdinaryModelClosureBundleReceipt
    scalingReplicationBundle : Plan.ScalingReplicationBundleReceipt
    apparatusCarrier : String

    sourceCarrierMatches :
      Plan.FullSourceGeometryBundleReceipt.apparatusCarrier sourceBundle
        ≡ apparatusCarrier
    phaseCarrierMatches :
      Plan.PhaseProbeBundleReceipt.apparatusCarrier phaseProbeBundle
        ≡ apparatusCarrier
    ordinaryCarrierMatches :
      Plan.OrdinaryModelClosureBundleReceipt.apparatusCarrier ordinaryModelBundle
        ≡ apparatusCarrier
    scalingCarrierMatches :
      Plan.ScalingReplicationBundleReceipt.apparatusCarrier scalingReplicationBundle
        ≡ apparatusCarrier

open SameApparatusExperimentalCut public

record ComparativeAnomalyReceipt
    (claim : Anti.AntigravityClaim) : Set where
  constructor comparative-anomaly-receipt
  field
    experimentalCut : SameApparatusExperimentalCut
    theoryComparison : Claim.ClaimIndexedTheoryComparison claim

    ordinaryResidualClosed :
      Unified.ordinaryResidualClosed (Claim.comparison theoryComparison) ≡ true

    alternativeResidualSmaller :
      Unified.modifiedResidualSmaller (Claim.comparison theoryComparison) ≡ true

    comparisonCarrier : String
    residualBudgetCarrier : String

open ComparativeAnomalyReceipt public

------------------------------------------------------------------------
-- What this receipt can and cannot promote.
------------------------------------------------------------------------

data AntigravityResearchStatus : Set where
  experimentalCutOpen : AntigravityResearchStatus
  attributedComparisonOpen : AntigravityResearchStatus
  comparativeAnomalyEstablished : AntigravityResearchStatus
  mechanismAttributionOpen : AntigravityResearchStatus
  independentTheoryRevisionRequired : AntigravityResearchStatus

statusFromComparativeAnomaly :
  {claim : Anti.AntigravityClaim} →
  ComparativeAnomalyReceipt claim → AntigravityResearchStatus
statusFromComparativeAnomaly receipt = comparativeAnomalyEstablished

------------------------------------------------------------------------
-- Residuals beyond a successful comparative anomaly.  Better fit does not
-- identify a unique mechanism, establish a universal law, or grant authority to
-- relabel every anomalous force as antigravity.
------------------------------------------------------------------------

data PostComparisonResidual : Set where
  missingMechanismSpecificAttribution : PostComparisonResidual
  missingIndependentTheoryReplication : PostComparisonResidual
  missingCrossApparatusGenerality : PostComparisonResidual
  missingAlternativeLawScope : PostComparisonResidual
  unresolvedOrdinaryModelRevision : PostComparisonResidual

producerForPostComparisonResidual :
  PostComparisonResidual → Search.ProducerClass
producerForPostComparisonResidual missingMechanismSpecificAttribution =
  Search.discriminatorProducer
producerForPostComparisonResidual missingIndependentTheoryReplication =
  Search.empiricalEvidenceProducer
producerForPostComparisonResidual missingCrossApparatusGenerality =
  Search.empiricalEvidenceProducer
producerForPostComparisonResidual missingAlternativeLawScope =
  Search.propositionSourceProducer
producerForPostComparisonResidual unresolvedOrdinaryModelRevision =
  Search.contradictionProducer

------------------------------------------------------------------------
-- No canonical inhabitant is supplied: current repo content gives experiment
-- designs, public constraints and source/proof machinery, not the four required
-- same-apparatus empirical bundle receipts plus a positive comparative anomaly.
------------------------------------------------------------------------

data CurrentComparativeAnomalyAuthority : Set where

noCurrentCanonicalComparativeAnomaly :
  CurrentComparativeAnomalyAuthority → ⊥
noCurrentCanonicalComparativeAnomaly ()

record AntigravityResearchPromotionBoundary : Set where
  constructor antigravity-research-promotion-boundary
  field
    sameApparatusExperimentalCutRequired : Bool
    claimIndexedAttributedComparisonRequired : Bool
    ordinaryResidualClosureRequired : Bool
    smallerAlternativeResidualRequired : Bool
    comparativeAnomalyEqualsUniqueMechanismProof : Bool
    comparativeAnomalyEqualsUniversalAntigravityLaw : Bool
    comparativeAnomalyMayJustifyMechanismSpecificFollowup : Bool
    currentRepoContainsCanonicalPositiveComparativeAnomaly : Bool
    proofSearchScheduleEqualsEmpiricalResult : Bool

canonicalAntigravityResearchPromotionBoundary :
  AntigravityResearchPromotionBoundary
canonicalAntigravityResearchPromotionBoundary =
  antigravity-research-promotion-boundary
    true true true true false false true false false
