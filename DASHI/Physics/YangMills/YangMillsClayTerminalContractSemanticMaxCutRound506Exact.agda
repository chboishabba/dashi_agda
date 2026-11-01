{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayTerminalContractSemanticMaxCutRound506Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND506: TERMINAL CONTRACT SEMANTIC MAX-CUT
--
-- Source/analytic theorems and endpoint semantics are deliberately separate.
-- R469's terminal record still consumes opaque predicates from the literal Clay
-- vocabulary.  This file enumerates exactly those endpoint interpretations that
-- are not constructor-choice equalities.
--
-- The entries below are semantic leaves, not claims that new independent
-- analytic estimates are required.  A single source theorem may discharge
-- several of them once its literal interpretation is proved.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Structural endpoint semantics.
------------------------------------------------------------------------

literalCompactSimpleGroupSemanticsLevel : ProofLevel
literalCompactSimpleGroupSemanticsLevel = conditional

literalFourDimensionalEuclideanSpacetimeSemanticsLevel : ProofLevel
literalFourDimensionalEuclideanSpacetimeSemanticsLevel = conditional

literalCompactSimpleParameterizationPreservedSemanticsLevel : ProofLevel
literalCompactSimpleParameterizationPreservedSemanticsLevel = conditional

------------------------------------------------------------------------
-- T1 / finite weak-coupling RG endpoint semantics.
------------------------------------------------------------------------

literalFiniteVolumeCutoffMeasureSemanticsLevel : ProofLevel
literalFiniteVolumeCutoffMeasureSemanticsLevel = conditional

literalReflectionPositiveRegularizationSemanticsLevel : ProofLevel
literalReflectionPositiveRegularizationSemanticsLevel = conditional

literalUltravioletYangMillsNormalizationSemanticsLevel : ProofLevel
literalUltravioletYangMillsNormalizationSemanticsLevel = conditional

literalAsymptoticallyFreeScaleTrajectorySemanticsLevel : ProofLevel
literalAsymptoticallyFreeScaleTrajectorySemanticsLevel = conditional

literalGaugeSymmetryPreservedSemanticsLevel : ProofLevel
literalGaugeSymmetryPreservedSemanticsLevel = conditional

literalLocalityPreservedSemanticsLevel : ProofLevel
literalLocalityPreservedSemanticsLevel = conditional

literalEuclideanCovariancePreservedSemanticsLevel : ProofLevel
literalEuclideanCovariancePreservedSemanticsLevel = conditional

literalReflectionPositivityPreservedSemanticsLevel : ProofLevel
literalReflectionPositivityPreservedSemanticsLevel = conditional

literalPositivityNormalizationPreservedSemanticsLevel : ProofLevel
literalPositivityNormalizationPreservedSemanticsLevel = conditional

literalVolumeCutoffCompatibilitySemanticsLevel : ProofLevel
literalVolumeCutoffCompatibilitySemanticsLevel = conditional

------------------------------------------------------------------------
-- T3 semantic interpretations not already represented by A3 continuum /
-- Schwinger-belonging leaves.
------------------------------------------------------------------------

literalAcceptedWightmanOrOSAxiomsSemanticsLevel : ProofLevel
literalAcceptedWightmanOrOSAxiomsSemanticsLevel = conditional

literalReconstructedHilbertSpaceSemanticsLevel : ProofLevel
literalReconstructedHilbertSpaceSemanticsLevel = conditional

literalPositiveSelfAdjointHamiltonianSemanticsLevel : ProofLevel
literalPositiveSelfAdjointHamiltonianSemanticsLevel = conditional

------------------------------------------------------------------------
-- T4 / local-QFT endpoint vocabulary.
------------------------------------------------------------------------

literalGaugeInvariantLocalObservableSemanticsLevel : ProofLevel
literalGaugeInvariantLocalObservableSemanticsLevel = conditional

literalCurvatureOperatorCorrespondenceSemanticsLevel : ProofLevel
literalCurvatureOperatorCorrespondenceSemanticsLevel = conditional

literalCurvatureOperatorGaugeInvariantSemanticsLevel : ProofLevel
literalCurvatureOperatorGaugeInvariantSemanticsLevel = conditional

literalCurvatureOperatorLocalitySemanticsLevel : ProofLevel
literalCurvatureOperatorLocalitySemanticsLevel = conditional

literalShortDistanceAsymptoticFreedomSemanticsLevel : ProofLevel
literalShortDistanceAsymptoticFreedomSemanticsLevel = conditional

literalStressTensorAndOPESemanticsLevel : ProofLevel
literalStressTensorAndOPESemanticsLevel = conditional

literalPhysicalOPECoefficientSemanticsLevel : ProofLevel
literalPhysicalOPECoefficientSemanticsLevel = conditional

literalPhysicalOPERemainderSemanticsLevel : ProofLevel
literalPhysicalOPERemainderSemanticsLevel = conditional

round506TerminalSemanticInventoryCompilerLevel : ProofLevel
round506TerminalSemanticInventoryCompilerLevel = machineChecked
