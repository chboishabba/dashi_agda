{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayExhaustiveResearchQueuesRound508Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND508: EXHAUSTIVE RESEARCH QUEUES
--
-- R496 has 68 live leaves.  R507 classifies them by proof shape.  R508 makes
-- the resulting max-cut operational:
--
--   18 source-analysis leaves
--   19 source<->literal attachment/transport leaves
--   31 opaque endpoint-semantic leaves
--
-- Total = 68.  The point is not that semantic/attachment leaves are trivial;
-- it is that they should not distract the hard-math search until their source
-- objects exist.  Conversely, no source theorem automatically inhabits an
-- opaque endpoint predicate without an explicit interpretation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves =
    R496.a1WilsonHessianVariation
  ∷ R496.a1AveragingConstraintVariation
  ∷ R496.a1GaugeProjectionVariation
  ∷ R496.a1WQRAssembly
  ∷ R496.a1ConstrainedGaussianMixedCoefficient
  ∷ R496.a1PhysicalJetFiveChannelSplit
  ∷ R496.a1FourJointReceiptEvaluation
  ∷ R496.a3FiniteFamilyContinuumLimit
  ∷ R496.a3ProjectiveEventExpectationConsistency
  ∷ R496.a3ContinuityAtEmpty
  ∷ R496.a4FiniteRegularityFromQuantitativeBounds
  ∷ R496.a5FiniteGrowthFromQuantitativeBounds
  ∷ R496.bWilsonTwoMarkExpansion
  ∷ R496.bWilsonConnectingWeightTail
  ∷ R496.bSameHamiltonianTransferCoordinate
  ∷ R496.c1MarkedSourceHilbertModulus
  ∷ R496.c4LiteralDensityMetricDerivative
  ∷ R496.g1ArbitraryCompactSimpleSourceMap
  ∷ []

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves =
    R496.aFiniteEuclideanSameObjectAttachment
  ∷ R496.aFiniteBosonicSameObjectAttachment
  ∷ R496.aFiniteWilsonRPSameObjectAttachment
  ∷ R496.a2BetaMarkGeneratedHistoryShell
  ∷ R496.a3StressDensityIsLiteralFiniteMeasure
  ∷ R496.a3LiteralSchwingerBelongs
  ∷ R496.a3SourceOSIsLiteralSchwinger
  ∷ R496.a3CylinderEventIndicatorSemantics
  ∷ R496.a3CylinderExpectationIntegralIdentification
  ∷ R496.a45QuantitativeFiniteExpectationAttachment
  ∷ R496.a4RepresentedRegularityExtensionality
  ∷ R496.a5RepresentedGrowthExtensionality
  ∷ R496.c1CurvatureGaugeLocalSemantics
  ∷ R496.c2PhysicalRemainderIsCompositeTail
  ∷ R496.c3OneStepAFRGIdentification
  ∷ R496.c4FiniteStressInsertionIsCMP119Local
  ∷ R496.c4StressCompletionIsCompletedMarkedStress
  ∷ R496.c4CompletedStressIsClayStress
  ∷ R496.c4DensityAnchoredLaneInstantiation
  ∷ []

endpointSemanticLeaves : List R496.ResidualLeaf
endpointSemanticLeaves =
    R496.structuralCompactSimpleSemantics
  ∷ R496.structuralFourDimensionalEuclideanSemantics
  ∷ R496.structuralCompactSimpleParameterizationSemantics
  ∷ R496.t1FiniteVolumeCutoffMeasureSemantics
  ∷ R496.t1ReflectionPositiveRegularizationSemantics
  ∷ R496.t1UltravioletNormalizationSemantics
  ∷ R496.t1AsymptoticallyFreeTrajectorySemantics
  ∷ R496.t1GaugeSymmetryPreservedSemantics
  ∷ R496.t1LocalityPreservedSemantics
  ∷ R496.t1EuclideanCovariancePreservedSemantics
  ∷ R496.t1ReflectionPositivityPreservedSemantics
  ∷ R496.t1PositivityNormalizationPreservedSemantics
  ∷ R496.t1VolumeCutoffCompatibilitySemantics
  ∷ R496.t3AcceptedWightmanOrOSSemantics
  ∷ R496.t3ReconstructedHilbertSpaceSemantics
  ∷ R496.t3PositiveSelfAdjointHamiltonianSemantics
  ∷ R496.t4GaugeInvariantLocalObservableSemantics
  ∷ R496.t4CurvatureCorrespondenceSemantics
  ∷ R496.t4CurvatureGaugeInvariantSemantics
  ∷ R496.t4CurvatureLocalitySemantics
  ∷ R496.t4ShortDistanceAFSemantics
  ∷ R496.t4StressTensorAndOPESemantics
  ∷ R496.t4PhysicalOPECoefficientSemantics
  ∷ R496.t4PhysicalOPERemainderSemantics
  ∷ R496.bVacuumSectorPositiveEnergySemantics
  ∷ R496.bStrictPositiveMassGapSemantics
  ∷ R496.bPhysicalScaleLowerBoundSemantics
  ∷ R496.bNoSpectralPollutionSemantics
  ∷ R496.bGapAndClusteringDerivedSemantics
  ∷ R496.g2WitnessIsLiteralNontriviality
  ∷ R496.g2WitnessPreservedInLiteralLimit
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount =
  listLength sourceLiteralAttachmentLeaves

endpointSemanticLeafCount : Nat
endpointSemanticLeafCount = listLength endpointSemanticLeaves

------------------------------------------------------------------------
-- Preferred attack order among genuine source-analysis leaves.
--
-- This is deliberately a queue, not a logical claim that later leaves depend
-- on every earlier leaf.  It keeps work concentrated on theorem-producing
-- bottlenecks rather than opaque endpoint vocabulary.
------------------------------------------------------------------------

preferredSourceAttackOrder : List R496.ResidualLeaf
preferredSourceAttackOrder =
    -- Representation theorem spine.
    R496.a3ContinuityAtEmpty
  ∷ R496.a3ProjectiveEventExpectationConsistency
  ∷ R496.a3FiniteFamilyContinuumLimit

    -- Source-correct Wilson/spectral B.
  ∷ R496.bWilsonTwoMarkExpansion
  ∷ R496.bWilsonConnectingWeightTail
  ∷ R496.bSameHamiltonianTransferCoordinate

    -- Quantitative finite OS0/OS5.
  ∷ R496.a4FiniteRegularityFromQuantitativeBounds
  ∷ R496.a5FiniteGrowthFromQuantitativeBounds

    -- Current-step RG/source A1.
  ∷ R496.a1WilsonHessianVariation
  ∷ R496.a1AveragingConstraintVariation
  ∷ R496.a1GaugeProjectionVariation
  ∷ R496.a1WQRAssembly
  ∷ R496.a1ConstrainedGaussianMixedCoefficient
  ∷ R496.a1PhysicalJetFiveChannelSplit
  ∷ R496.a1FourJointReceiptEvaluation

    -- Local QFT and all-G closure.
  ∷ R496.c1MarkedSourceHilbertModulus
  ∷ R496.c4LiteralDensityMetricDerivative
  ∷ R496.g1ArbitraryCompactSimpleSourceMap
  ∷ []

allSixtyEightLeavesStillExplicit : Bool
allSixtyEightLeavesStillExplicit = false

-- false means: do not treat the 68-item count as "68 independent hard
-- analytic lemmas"; R508 explicitly decomposes the work by proof shape.
sixtyEightIndependentHardAnalyticLemmas : Bool
sixtyEightIndependentHardAnalyticLemmas = false

round508ResearchQueueCompilerLevel : ProofLevel
round508ResearchQueueCompilerLevel = machineChecked
