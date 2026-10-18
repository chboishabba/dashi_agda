{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayExhaustiveResidualClassificationRound507Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND507: EXHAUSTIVE RESIDUAL CLASSIFICATION
--
-- R496 is the exhaustive 68-leaf Clay board.  R507 adds the distinction that
-- matters for proof search:
--
--   sourceAnalysis
--     a genuine mathematical/source theorem or estimate;
--
--   sourceLiteralAttachment
--     identify a proved/source object with the literal physical carrier or
--     transfer a property across that identification;
--
--   endpointSemantics
--     inhabit an opaque predicate of LiteralYangMillsSemantics.
--
-- None of these classes licenses promotion by name alone.  In particular,
-- endpoint semantics are not "proved" merely because a similarly named source
-- theorem exists.  Conversely, constructor-choice equalities are absent from
-- R496 and therefore from this classification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496

data ResidualKind : Set where
  sourceAnalysis : ResidualKind
  sourceLiteralAttachment : ResidualKind
  endpointSemantics : ResidualKind

kind : R496.ResidualLeaf → ResidualKind

-- Structural / T1 / T3 / T4 literal contract: predicates are opaque in S.
kind R496.structuralCompactSimpleSemantics = endpointSemantics
kind R496.structuralFourDimensionalEuclideanSemantics = endpointSemantics
kind R496.structuralCompactSimpleParameterizationSemantics = endpointSemantics
kind R496.t1FiniteVolumeCutoffMeasureSemantics = endpointSemantics
kind R496.t1ReflectionPositiveRegularizationSemantics = endpointSemantics
kind R496.t1UltravioletNormalizationSemantics = endpointSemantics
kind R496.t1AsymptoticallyFreeTrajectorySemantics = endpointSemantics
kind R496.t1GaugeSymmetryPreservedSemantics = endpointSemantics
kind R496.t1LocalityPreservedSemantics = endpointSemantics
kind R496.t1EuclideanCovariancePreservedSemantics = endpointSemantics
kind R496.t1ReflectionPositivityPreservedSemantics = endpointSemantics
kind R496.t1PositivityNormalizationPreservedSemantics = endpointSemantics
kind R496.t1VolumeCutoffCompatibilitySemantics = endpointSemantics
kind R496.t3AcceptedWightmanOrOSSemantics = endpointSemantics
kind R496.t3ReconstructedHilbertSpaceSemantics = endpointSemantics
kind R496.t3PositiveSelfAdjointHamiltonianSemantics = endpointSemantics
kind R496.t4GaugeInvariantLocalObservableSemantics = endpointSemantics
kind R496.t4CurvatureCorrespondenceSemantics = endpointSemantics
kind R496.t4CurvatureGaugeInvariantSemantics = endpointSemantics
kind R496.t4CurvatureLocalitySemantics = endpointSemantics
kind R496.t4ShortDistanceAFSemantics = endpointSemantics
kind R496.t4StressTensorAndOPESemantics = endpointSemantics
kind R496.t4PhysicalOPECoefficientSemantics = endpointSemantics
kind R496.t4PhysicalOPERemainderSemantics = endpointSemantics

-- Published finite OS theorems exist; only literal-family attachment remains.
kind R496.aFiniteEuclideanSameObjectAttachment = sourceLiteralAttachment
kind R496.aFiniteBosonicSameObjectAttachment = sourceLiteralAttachment
kind R496.aFiniteWilsonRPSameObjectAttachment = sourceLiteralAttachment

-- A1 is actual current-step source mathematics.
kind R496.a1WilsonHessianVariation = sourceAnalysis
kind R496.a1AveragingConstraintVariation = sourceAnalysis
kind R496.a1GaugeProjectionVariation = sourceAnalysis
kind R496.a1WQRAssembly = sourceAnalysis
kind R496.a1ConstrainedGaussianMixedCoefficient = sourceAnalysis
kind R496.a1PhysicalJetFiveChannelSplit = sourceAnalysis
kind R496.a1FourJointReceiptEvaluation = sourceAnalysis

-- A2 is a physical source-coordinate identification, not a model-choice refl.
kind R496.a2BetaMarkGeneratedHistoryShell = sourceLiteralAttachment

-- A3 source-native / represented continuum.
kind R496.a3StressDensityIsLiteralFiniteMeasure = sourceLiteralAttachment
kind R496.a3FiniteFamilyContinuumLimit = sourceAnalysis
kind R496.a3LiteralSchwingerBelongs = sourceLiteralAttachment
kind R496.a3SourceOSIsLiteralSchwinger = sourceLiteralAttachment
kind R496.a3CylinderEventIndicatorSemantics = sourceLiteralAttachment
kind R496.a3ProjectiveEventExpectationConsistency = sourceAnalysis
kind R496.a3ContinuityAtEmpty = sourceAnalysis
kind R496.a3CylinderExpectationIntegralIdentification = sourceLiteralAttachment

-- A4/A5: one family attachment, two estimates, two extensional transports.
kind R496.a45QuantitativeFiniteExpectationAttachment = sourceLiteralAttachment
kind R496.a4FiniteRegularityFromQuantitativeBounds = sourceAnalysis
kind R496.a5FiniteGrowthFromQuantitativeBounds = sourceAnalysis
kind R496.a4RepresentedRegularityExtensionality = sourceLiteralAttachment
kind R496.a5RepresentedGrowthExtensionality = sourceLiteralAttachment

-- B: Wilson two-mark mathematics + same-H calibration; then literal semantics.
kind R496.bWilsonTwoMarkExpansion = sourceAnalysis
kind R496.bWilsonConnectingWeightTail = sourceAnalysis
kind R496.bSameHamiltonianTransferCoordinate = sourceAnalysis
kind R496.bVacuumSectorPositiveEnergySemantics = endpointSemantics
kind R496.bStrictPositiveMassGapSemantics = endpointSemantics
kind R496.bPhysicalScaleLowerBoundSemantics = endpointSemantics
kind R496.bNoSpectralPollutionSemantics = endpointSemantics
kind R496.bGapAndClusteringDerivedSemantics = endpointSemantics

-- C: physical marked/composite source facts and same-object identifications.
kind R496.c1MarkedSourceHilbertModulus = sourceAnalysis
kind R496.c1CurvatureGaugeLocalSemantics = sourceLiteralAttachment
kind R496.c2PhysicalRemainderIsCompositeTail = sourceLiteralAttachment
kind R496.c3OneStepAFRGIdentification = sourceLiteralAttachment
kind R496.c4FiniteStressInsertionIsCMP119Local = sourceLiteralAttachment
kind R496.c4StressCompletionIsCompletedMarkedStress = sourceLiteralAttachment
kind R496.c4CompletedStressIsClayStress = sourceLiteralAttachment
kind R496.c4LiteralDensityMetricDerivative = sourceAnalysis
kind R496.c4DensityAnchoredLaneInstantiation = sourceLiteralAttachment

-- G: arbitrary-G source construction, then literal nontriviality semantics.
kind R496.g1ArbitraryCompactSimpleSourceMap = sourceAnalysis
kind R496.g2WitnessIsLiteralNontriviality = endpointSemantics
kind R496.g2WitnessPreservedInLiteralLimit = endpointSemantics

------------------------------------------------------------------------
-- Proof-search phase.  This is a dependency/scheduling classification, not a
-- claim that leaves within a phase are logically equivalent.
------------------------------------------------------------------------

data ResidualPhase : Set where
  finiteSource : ResidualPhase
  representedContinuum : ResidualPhase
  spectralGap : ResidualPhase
  localQFT : ResidualPhase
  allGroupsNontriviality : ResidualPhase
  terminalInterpretation : ResidualPhase

phase : R496.ResidualLeaf → ResidualPhase

phase R496.structuralCompactSimpleSemantics = terminalInterpretation
phase R496.structuralFourDimensionalEuclideanSemantics = terminalInterpretation
phase R496.structuralCompactSimpleParameterizationSemantics = terminalInterpretation
phase R496.t1FiniteVolumeCutoffMeasureSemantics = terminalInterpretation
phase R496.t1ReflectionPositiveRegularizationSemantics = terminalInterpretation
phase R496.t1UltravioletNormalizationSemantics = terminalInterpretation
phase R496.t1AsymptoticallyFreeTrajectorySemantics = terminalInterpretation
phase R496.t1GaugeSymmetryPreservedSemantics = terminalInterpretation
phase R496.t1LocalityPreservedSemantics = terminalInterpretation
phase R496.t1EuclideanCovariancePreservedSemantics = terminalInterpretation
phase R496.t1ReflectionPositivityPreservedSemantics = terminalInterpretation
phase R496.t1PositivityNormalizationPreservedSemantics = terminalInterpretation
phase R496.t1VolumeCutoffCompatibilitySemantics = terminalInterpretation
phase R496.t3AcceptedWightmanOrOSSemantics = terminalInterpretation
phase R496.t3ReconstructedHilbertSpaceSemantics = terminalInterpretation
phase R496.t3PositiveSelfAdjointHamiltonianSemantics = terminalInterpretation
phase R496.t4GaugeInvariantLocalObservableSemantics = terminalInterpretation
phase R496.t4CurvatureCorrespondenceSemantics = terminalInterpretation
phase R496.t4CurvatureGaugeInvariantSemantics = terminalInterpretation
phase R496.t4CurvatureLocalitySemantics = terminalInterpretation
phase R496.t4ShortDistanceAFSemantics = terminalInterpretation
phase R496.t4StressTensorAndOPESemantics = terminalInterpretation
phase R496.t4PhysicalOPECoefficientSemantics = terminalInterpretation
phase R496.t4PhysicalOPERemainderSemantics = terminalInterpretation

phase R496.aFiniteEuclideanSameObjectAttachment = finiteSource
phase R496.aFiniteBosonicSameObjectAttachment = finiteSource
phase R496.aFiniteWilsonRPSameObjectAttachment = finiteSource
phase R496.a1WilsonHessianVariation = finiteSource
phase R496.a1AveragingConstraintVariation = finiteSource
phase R496.a1GaugeProjectionVariation = finiteSource
phase R496.a1WQRAssembly = finiteSource
phase R496.a1ConstrainedGaussianMixedCoefficient = finiteSource
phase R496.a1PhysicalJetFiveChannelSplit = finiteSource
phase R496.a1FourJointReceiptEvaluation = finiteSource
phase R496.a2BetaMarkGeneratedHistoryShell = finiteSource

phase R496.a3StressDensityIsLiteralFiniteMeasure = representedContinuum
phase R496.a3FiniteFamilyContinuumLimit = representedContinuum
phase R496.a3LiteralSchwingerBelongs = representedContinuum
phase R496.a3SourceOSIsLiteralSchwinger = representedContinuum
phase R496.a3CylinderEventIndicatorSemantics = representedContinuum
phase R496.a3ProjectiveEventExpectationConsistency = representedContinuum
phase R496.a3ContinuityAtEmpty = representedContinuum
phase R496.a3CylinderExpectationIntegralIdentification = representedContinuum
phase R496.a45QuantitativeFiniteExpectationAttachment = representedContinuum
phase R496.a4FiniteRegularityFromQuantitativeBounds = representedContinuum
phase R496.a5FiniteGrowthFromQuantitativeBounds = representedContinuum
phase R496.a4RepresentedRegularityExtensionality = representedContinuum
phase R496.a5RepresentedGrowthExtensionality = representedContinuum

phase R496.bWilsonTwoMarkExpansion = spectralGap
phase R496.bWilsonConnectingWeightTail = spectralGap
phase R496.bSameHamiltonianTransferCoordinate = spectralGap
phase R496.bVacuumSectorPositiveEnergySemantics = terminalInterpretation
phase R496.bStrictPositiveMassGapSemantics = terminalInterpretation
phase R496.bPhysicalScaleLowerBoundSemantics = terminalInterpretation
phase R496.bNoSpectralPollutionSemantics = terminalInterpretation
phase R496.bGapAndClusteringDerivedSemantics = terminalInterpretation

phase R496.c1MarkedSourceHilbertModulus = localQFT
phase R496.c1CurvatureGaugeLocalSemantics = localQFT
phase R496.c2PhysicalRemainderIsCompositeTail = localQFT
phase R496.c3OneStepAFRGIdentification = localQFT
phase R496.c4FiniteStressInsertionIsCMP119Local = localQFT
phase R496.c4StressCompletionIsCompletedMarkedStress = localQFT
phase R496.c4CompletedStressIsClayStress = localQFT
phase R496.c4LiteralDensityMetricDerivative = localQFT
phase R496.c4DensityAnchoredLaneInstantiation = localQFT

phase R496.g1ArbitraryCompactSimpleSourceMap = allGroupsNontriviality
phase R496.g2WitnessIsLiteralNontriviality = terminalInterpretation
phase R496.g2WitnessPreservedInLiteralLimit = terminalInterpretation

------------------------------------------------------------------------
-- Authoritative inherited board.
------------------------------------------------------------------------

allResidualLeaves = R496.residualLeaves

allResidualLeafCount : Nat
allResidualLeafCount = R496.residualLeafCount

constructorChoiceEqualityIsAResidualKind : Bool
constructorChoiceEqualityIsAResidualKind = false

opaqueEndpointPredicateMayBeDischargedBySimilarlyNamedSourceTheorem : Bool
opaqueEndpointPredicateMayBeDischargedBySimilarlyNamedSourceTheorem = false

round507ExhaustiveClassificationCompilerLevel : ProofLevel
round507ExhaustiveClassificationCompilerLevel = machineChecked
