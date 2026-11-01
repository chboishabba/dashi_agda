{-# OPTIONS --safe #-}
module DASHI.Unified.YMGoal1TOECompatibilityExact where

------------------------------------------------------------------------
-- YANG-MILLS GOAL-1 COMPATIBILITY ADAPTER FOR THE FOCUSED DASHI TOE GRAPH
--
-- O. Objective.
-- Reuse the current branch Goal-1 owners in the normalized TOE import graph.
--
-- R. Reuse.
-- R435 owns the canonical selected B source.
-- R436 owns the finite A source.
-- R437 owns the Clay-facing local-QFT C source.
-- R438 owns the literal CMP116 rate-source compatibility surface.
-- R439 owns the same-H nontriviality compiler boundary.
-- Existing closure modules own continuum, mass-gap, and Clay non-promotion.
--
-- C. Construction.
-- This module exports aliases only.
-- It proves no new Yang-Mills estimate.
--
-- S. Scope.
-- The later R559/R474 source-native route remains the preferred donor lineage.
-- This module is a compatibility adapter for this older branch.
--
-- L. Lane.
-- This file owns only the Goal-1 to TOE import edge.
-- It does not edit or import ESD implementation surfaces.
--
-- P. Postcondition.
-- TOE consumers can inspect the current Goal-1 frontier and exact non-promotion
-- facts through one normalized module.
--
-- G. Governance.
-- Original theorem owners retain attribution.
-- Conditional proof levels remain conditional.
-- A finite or conditional result does not promote continuum Yang-Mills.
--
-- F. Verification.
-- Read-back must preserve exact owner names and exact false promotion proofs.
-- Kernel certification requires an exact-head Agda or CI receipt.
--
-- Preconditions.
-- The R435--R439 owners exist on this branch.
-- The canonical current YM mass-gap and continuum boundaries exist.
--
-- Invariants.
-- No theorem changes proof level in this adapter.
-- No carrier identity is added.
-- No ESD surface is modified.
-- No meta-introspector theorem is copied or reattributed.
--
-- Postconditions.
-- The A, B, C, and same-H source levels are visible to the TOE graph.
-- Continuum transfer remains false.
-- Continuum mass-gap promotion remains false.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CanonicalASourceRound436Exact as R436
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as R437
import DASHI.Physics.YangMills.BalabanCMP116CanonicalLiteralRateSourceRound438Exact as R438
import DASHI.Physics.YangMills.YangMillsClayGoal1SameHNontrivialityRound439Exact as R439
import DASHI.Physics.YangMills.BalabanCMP116VariableDomainPreferredR415Round440Exact as R440
import DASHI.Physics.YangMills.BalabanCMP116R429RootedTraceCountingRound441Exact as R441
import DASHI.Physics.YangMills.BalabanCMP116R429TraceEntropyBudgetRound442Exact as R442
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as R443
import DASHI.Physics.YangMills.YangMillsCMP119PeterWeylWilsonSquareRound444Exact as R444
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119UniformProjectiveCompactnessExact as AProjective
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as AOS05
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as AFiniteLimit
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as C123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as C129
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as C131
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as COPE

import DASHI.Physics.Closure.YangMillsMassGapBoundary as MassGap
import DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary as Continuum
import DASHI.Physics.Closure.YMClayPromotionBoundary as Clay

------------------------------------------------------------------------
-- Exact current-branch source levels.
------------------------------------------------------------------------

goal1FiniteASourceLevel : ProofLevel
goal1FiniteASourceLevel =
  R436.literalRound436CanonicalASourceLevel

goal1CanonicalSelectedBSourceLevel : ProofLevel
goal1CanonicalSelectedBSourceLevel =
  R435.literalRound435CanonicalSelectedSourceLevel

goal1LiteralCMP116RateSourceLevel : ProofLevel
goal1LiteralCMP116RateSourceLevel =
  R438.literalRound438CanonicalCMP116RateTheoremLevel

goal1LocalQFTCSourceLevel : ProofLevel
goal1LocalQFTCSourceLevel =
  R437.literalRound437Goal1CSourceLevel

goal1SameHNontrivialitySemanticBridgeLevel : ProofLevel
goal1SameHNontrivialitySemanticBridgeLevel =
  R439.literalRound439SameSystemSemanticBridgeLevel


------------------------------------------------------------------------
-- Preferred current-branch Goal-1 cuts.
-- These supersede the coarse global-tree compatibility route where noted.
------------------------------------------------------------------------

goal1FiniteA1WilsonActionInvarianceLevel : ProofLevel
goal1FiniteA1WilsonActionInvarianceLevel =
  R443.literalRound443FiniteWilsonActionInvarianceLevel

goal1FiniteA1ProductHaarInvarianceLevel : ProofLevel
goal1FiniteA1ProductHaarInvarianceLevel =
  R443.literalRound443FiniteProductHaarInvarianceLevel

goal1FiniteA1DensityInvariantCompilerLevel : ProofLevel
goal1FiniteA1DensityInvariantCompilerLevel =
  R443.round443WilsonActionToDensityInvariantCompilerLevel

goal1FiniteA2PeterWeylWilsonIdentificationLevel : ProofLevel
goal1FiniteA2PeterWeylWilsonIdentificationLevel =
  R444.literalRound444PeterWeylWilsonIdentificationLevel

goal1FiniteA2SquareCompilerLevel : ProofLevel
goal1FiniteA2SquareCompilerLevel =
  R444.round444StandaloneWilsonSquareCompilerLevel

goal1PreferredVariableDomainBSourceLevel : ProofLevel
goal1PreferredVariableDomainBSourceLevel =
  R440.literalRound440VariableDomainCMP116SourceLevel

goal1R429RootedTraceEncodingLevel : ProofLevel
goal1R429RootedTraceEncodingLevel =
  R441.literalRound441R429RootedTraceEncodingLevel

goal1R429RootedTraceCountCompilerLevel : ProofLevel
goal1R429RootedTraceCountCompilerLevel =
  R441.round441InjectiveTraceShellCountCompilerLevel

goal1R429SourceDecayReserveLevel : ProofLevel
goal1R429SourceDecayReserveLevel =
  R442.literalRound442SourceDecayReserveLevel

goal1R429EntropyBudgetCompilerLevel : ProofLevel
goal1R429EntropyBudgetCompilerLevel =
  R442.round442R429ShellEntropyBudgetCompilerLevel

legacyGlobalTreeMetricPreferred : Bool
legacyGlobalTreeMetricPreferred = false

legacyGlobalTreeMetricPreferredIsFalse :
  legacyGlobalTreeMetricPreferred ≡ false
legacyGlobalTreeMetricPreferredIsFalse = refl

variableDomainR440Preferred : Bool
variableDomainR440Preferred = true

variableDomainR440PreferredIsTrue :
  variableDomainR440Preferred ≡ true
variableDomainR440PreferredIsTrue = refl


------------------------------------------------------------------------
-- Reused A3/A4/A5 continuum and regularity owners.
------------------------------------------------------------------------

goal1A3UniformCompactContainmentLevel : ProofLevel
goal1A3UniformCompactContainmentLevel =
  AProjective.literalCMP119UniformCompactContainmentLevel

goal1A3ExtractedClusterCylinderAgreementLevel : ProofLevel
goal1A3ExtractedClusterCylinderAgreementLevel =
  AProjective.literalCMP119ExtractedClusterCylinderAgreementLevel

goal1A3TightnessSubsequenceCompilerLevel : ProofLevel
goal1A3TightnessSubsequenceCompilerLevel =
  AProjective.cmp119UniformTightnessSubsequenceCompilerLevel

goal1A4FiniteRegularityLevel : ProofLevel
goal1A4FiniteRegularityLevel =
  AOS05.literalCMP119FiniteRegularityLevel

goal1A5FiniteGrowthControlLevel : ProofLevel
goal1A5FiniteGrowthControlLevel =
  AOS05.literalCMP119FiniteGrowthControlLevel

goal1A45OSLimitCompilerLevel : ProofLevel
goal1A45OSLimitCompilerLevel =
  AOS05.canonicalOS05LimitAssemblyLevel

goal1AExpectationLimitCompilerLevel : ProofLevel
goal1AExpectationLimitCompilerLevel =
  AFiniteLimit.finitePhysicalExpectationLimitCompilerLevel

goal1ANormalizationCompilerLevel : ProofLevel
goal1ANormalizationCompilerLevel =
  AFiniteLimit.continuumPhysicalMeasureNormalizationCompilerLevel

------------------------------------------------------------------------
-- Reused C3/C4 same-family owners.
------------------------------------------------------------------------

goal1C3OneStepAFIdentificationLevel : ProofLevel
goal1C3OneStepAFIdentificationLevel =
  COPE.physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel

goal1C3AllDepthCoefficientCompilerLevel : ProofLevel
goal1C3AllDepthCoefficientCompilerLevel =
  COPE.coefficientRGRecurrenceUniquenessLevel

goal1C4DensityAnchoredStressInstantiationLevel : ProofLevel
goal1C4DensityAnchoredStressInstantiationLevel =
  C123.literalDensityAnchoredStressLaneInstantiationLevel

goal1C4DensityAnchoredStressCompilerLevel : ProofLevel
goal1C4DensityAnchoredStressCompilerLevel =
  C123.densityAnchoredCanonicalMetricStressLaneCompilerLevel

goal1C4SectorRecoveryCompilerLevel : ProofLevel
goal1C4SectorRecoveryCompilerLevel =
  C129.balabanSectorQFTRecoveryExportCompilerLevel

goal1C4LiteralSectorRecoveryLevel : ProofLevel
goal1C4LiteralSectorRecoveryLevel =
  C129.literalBalabanSectorQFTRecoveryExportLevel

goal1C4CommonMetricCompilerLevel : ProofLevel
goal1C4CommonMetricCompilerLevel =
  C131.commonMetricReadyBalabanSectorCompilerLevel

goal1C4LiteralCommonMetricRecoveryLevel : ProofLevel
goal1C4LiteralCommonMetricRecoveryLevel =
  C131.literalCommonMetricReadyBalabanSectorLevel

------------------------------------------------------------------------
-- Exact non-promotion theorem reuse.
------------------------------------------------------------------------

flat4DContinuumTransferProvedHere : Bool
flat4DContinuumTransferProvedHere =
  Continuum.flat4DContinuumTransferProvedHere

continuumMassGapPromoted : Bool
continuumMassGapPromoted =
  Continuum.continuumMassGapPromoted

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  Clay.clayYangMillsPromoted


yangMillsMassGapBoundaryStillNotPromoted :
  MassGap.YangMillsMassGapBoundaryReceipt.massGapPromoted
    MassGap.canonicalYangMillsMassGapBoundaryReceipt
  ≡ false
yangMillsMassGapBoundaryStillNotPromoted =
  MassGap.YangMillsMassGapBoundaryReceipt.massGapPromotedIsFalse
    MassGap.canonicalYangMillsMassGapBoundaryReceipt

flat4DContinuumTransferStillOpen :
  flat4DContinuumTransferProvedHere ≡ false
flat4DContinuumTransferStillOpen =
  Continuum.flat4DContinuumTransferProvedHereIsFalse

continuumMassGapStillNotPromoted :
  continuumMassGapPromoted ≡ false
continuumMassGapStillNotPromoted =
  Continuum.continuumMassGapPromotedIsFalse

clayYangMillsStillNotPromoted :
  clayYangMillsPromoted ≡ false
clayYangMillsStillNotPromoted =
  Clay.ClayPromotionBoundary.noClayPromotion
    Clay.clayPromotionBoundary

------------------------------------------------------------------------
-- ZKP frame.
------------------------------------------------------------------------

record YMGoal1TOEZKPFrame : Set where
  field
    objective : String
    reuseRule : String
    constructionRule : String
    scopeRule : String
    laneRule : String
    postconditionRule : String
    governanceRule : String
    verificationRule : String

    ownersExist : Bool
    ownersExistIsTrue : ownersExist ≡ true

    noNewScientificTheorem : Bool
    noNewScientificTheoremIsTrue : noNewScientificTheorem ≡ true

    laterSourceNativeRoutePreferred : Bool
    laterSourceNativeRoutePreferredIsTrue :
      laterSourceNativeRoutePreferred ≡ true

    continuumPromotionBlocked : Bool
    continuumPromotionBlockedIsFalse :
      continuumPromotionBlocked ≡ false

    clayPromotionBlocked : Bool
    clayPromotionBlockedIsFalse :
      clayPromotionBlocked ≡ false

open YMGoal1TOEZKPFrame public

canonicalYMGoal1TOEZKPFrame : YMGoal1TOEZKPFrame
canonicalYMGoal1TOEZKPFrame = record
  { objective =
      "Reuse current Goal-1 theorem owners in the focused DASHI TOE graph."
  ; reuseRule =
      "Reuse canonical theorem owners before adding adapters."
  ; constructionRule =
      "Export aliases and exact non-promotion proofs only."
  ; scopeRule =
      "Use R440 variable-domain d_k(Y), R441 rooted traces, R442 entropy, R443 Haar action, and R444 Peter-Weyl as the preferred current-branch route. Treat R438 global-tree geometry as compatibility only. Prefer later R474/R559 source-native owners when available."
  ; laneRule =
      "Keep Yang-Mills theorem ownership in the Yang-Mills lane and keep ESD surfaces unchanged."
  ; postconditionRule =
      "Expose A/B/C/same-H frontier levels and exact continuum, mass-gap, and Clay non-promotion facts."
  ; governanceRule =
      "Preserve attribution, proof levels, carrier distinctions, and fail-closed promotion."
  ; verificationRule =
      "Require exact-head preflight and Agda receipts before any kernel-green claim."
  ; ownersExist = true
  ; ownersExistIsTrue = refl
  ; noNewScientificTheorem = true
  ; noNewScientificTheoremIsTrue = refl
  ; laterSourceNativeRoutePreferred = true
  ; laterSourceNativeRoutePreferredIsTrue = refl
  ; continuumPromotionBlocked = flat4DContinuumTransferProvedHere
  ; continuumPromotionBlockedIsFalse = flat4DContinuumTransferStillOpen
  ; clayPromotionBlocked = clayYangMillsPromoted
  ; clayPromotionBlockedIsFalse = clayYangMillsStillNotPromoted
  }
