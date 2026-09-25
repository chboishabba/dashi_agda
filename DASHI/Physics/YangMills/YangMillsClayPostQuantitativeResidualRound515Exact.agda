{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND515: RESIDUAL AFTER CONCRETE FINITE OS0/OS5 BOUNDS
--
-- R514 chooses the finite A4/A5 predicates to be the actual T5 quantitative
-- moment/growth statements and proves them from the source producer after the
-- SAME-family expectation attachment.
--
-- Therefore the former source-analysis leaves
--
--   a4FiniteRegularityFromQuantitativeBounds
--   a5FiniteGrowthFromQuantitativeBounds
--
-- are compiler-owned.  Their source mathematics was already present in the
-- T5 exponential-moment producer.
--
-- Residual:
--   15 source-analysis
--   18 source<->literal attachment
--   21 endpoint semantics (structural/T1/T4)
--   ----------------------------------------
--   54 total
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as R514

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves =
    R496.a1WilsonHessianVariation
  ∷ R496.a1AveragingConstraintVariation
  ∷ R496.a1GaugeProjectionVariation
  ∷ R496.a1WQRAssembly
  ∷ R496.a1ConstrainedGaussianMixedCoefficient
  ∷ R496.a1PhysicalJetFiveChannelSplit
  ∷ R496.a1FourJointReceiptEvaluation
  ∷ R496.a3ProjectiveEventExpectationConsistency
  ∷ R496.a3ContinuityAtEmpty
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
  ∷ R496.t4GaugeInvariantLocalObservableSemantics
  ∷ R496.t4CurvatureCorrespondenceSemantics
  ∷ R496.t4CurvatureGaugeInvariantSemantics
  ∷ R496.t4CurvatureLocalitySemantics
  ∷ R496.t4ShortDistanceAFSemantics
  ∷ R496.t4StressTensorAndOPESemantics
  ∷ R496.t4PhysicalOPECoefficientSemantics
  ∷ R496.t4PhysicalOPERemainderSemantics
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount = listLength sourceLiteralAttachmentLeaves

endpointSemanticLeafCount : Nat
endpointSemanticLeafCount = listLength endpointSemanticLeaves

residualLeafCount : Nat
residualLeafCount =
  sourceAnalysisLeafCount + sourceLiteralAttachmentLeafCount + endpointSemanticLeafCount
  where
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)

finiteRegularityAdditionalAnalysisStillResidual : Bool
finiteRegularityAdditionalAnalysisStillResidual = false

finiteGrowthAdditionalAnalysisStillResidual : Bool
finiteGrowthAdditionalAnalysisStillResidual = false

quantitativeSameFamilyAttachmentStillResidual : Bool
quantitativeSameFamilyAttachmentStillResidual = true

round515PostQuantitativeResidualCompilerLevel : ProofLevel
round515PostQuantitativeResidualCompilerLevel = machineChecked
