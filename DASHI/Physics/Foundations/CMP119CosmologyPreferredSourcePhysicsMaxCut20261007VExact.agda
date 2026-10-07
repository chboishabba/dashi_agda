{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261007VExact where

------------------------------------------------------------------------
-- OVERLAY V / 2026-10-07: SOURCE-THEOREM MAX-CUT.
--
-- This supersedes U as the preferred accounting surface.
--
-- S1: CMP119 already publishes Euclidean covariance of the regular E_j source
--     (2.29), including the B-coordinate form (3.58). Do NOT re-prove that.
--     The genuine source work is the same-object weld from the repository's
--     abstract CMP109/116 Background/tangent to that literal B-coordinate and
--     the ten canonical metric/source directions. Variational uniqueness is a
--     valid optional producer of background naturality, not a second premise.
--
-- S2: once the renormalized Hilbert/Weyl identity is stated on the exact
--     stress/F2 operator pair, authority-record instantiation is compiler-only.
--
-- S3a: CMP116 already publishes differentiated analytic localization and the
--      (1.26)--(1.29) positive rate split. Geometric summation and weighted
--      Cauchy/Hilbert transport are compiler-owned. The novel payment is only
--      same-object binding of the selected F2 mark to those source coordinates
--      with uniform positive radii/constants and gauge/local semantics.
--
-- S3b: first instantiate the LITERAL finite Eq.(1.71) fibre/density/integral.
--      Exact Haar masses erase discrepancy. Direct oscillation convergence is
--      not primitive: a uniform Eq.(1.71) Lipschitz cell bound plus a vanishing
--      product-Haar mesh compiles to oscillation -> 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanBackgroundMinimizerSymmetryNaturalityExact as Variational
import DASHI.Physics.Foundations.CMP119CosmologyP1PublishedEuclideanBackgroundCovarianceExact as S1
import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact as S2
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact as S3F2
import DASHI.Physics.Foundations.CMP119CosmologyP3CMP116MarkedF2SourceMaxCutExact as S3Source
import DASHI.Physics.Foundations.CMP119CosmologyP3Equation171LiteralRealizationMaxCutExact as S3Eq171
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateMassWeightedHaarExact as S3Haar
import DASHI.Physics.Foundations.CMP119CosmologyP3ExactMassOscillationOnlyExact as ExactMass
import DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerExact as Lipschitz

------------------------------------------------------------------------
-- Terminal dependency-package accounting.
------------------------------------------------------------------------

remainingNovelSourcePackageCount : Nat
remainingNovelSourcePackageCount = 3

remainingStandardImportedAuthorityCount : Nat
remainingStandardImportedAuthorityCount = 3

remainingPreferredPackageCount : Nat
remainingPreferredPackageCount = 4

------------------------------------------------------------------------
-- S1: published Euclidean covariance + SAME-OBJECT source-coordinate weld.
------------------------------------------------------------------------

s1PublishedPotentialCovarianceNeedsFreshProof : Bool
s1PublishedPotentialCovarianceNeedsFreshProof =
  S1.publishedPotentialCovarianceNeedsFreshProof

s1SameObjectBackgroundAndTangentIdentificationRequired : Bool
s1SameObjectBackgroundAndTangentIdentificationRequired =
  S1.remainingS1WorkIsSameObjectBackgroundAndTangentIdentification

s1TenMetricDirectionsInPublishedBActionRequired : Bool
s1TenMetricDirectionsInPublishedBActionRequired =
  S1.remainingS1WorkIncludesTenMetricDirectionsInPublishedBAction

s1PrimitiveBackgroundEquivarianceRequired : Bool
s1PrimitiveBackgroundEquivarianceRequired =
  Variational.primitiveSelectedBackgroundEquivarianceRequired

s1VariationalNaturalityAvailableAsCompiler : Bool
s1VariationalNaturalityAvailableAsCompiler =
  Variational.backgroundNaturalityFollowsFromInvariantVariationalProblem

------------------------------------------------------------------------
-- S2: exact renormalized operator Ward identity.
------------------------------------------------------------------------

s2ExactRenormalizedOperatorIdentityRequired : Bool
s2ExactRenormalizedOperatorIdentityRequired =
  S2.remainingR2WorkIsExactRenormalizedOperatorIdentity

s2AuthorityRecordInstantiationRequired : Bool
s2AuthorityRecordInstantiationRequired =
  S2.remainingR2WorkIsInstantiationOfStandardWardAuthority

------------------------------------------------------------------------
-- S3a: ONE selected F2 mark; source decay/rate split already imported.
------------------------------------------------------------------------

s3SelectedMarkedF2SourceRequired : Bool
s3SelectedMarkedF2SourceRequired =
  S3F2.remainingSelectedF2SourceWorkIsPhysicalMarkedSourceDataAndSemantics

s3UniversalMarkedCurvatureFamilyRequired : Bool
s3UniversalMarkedCurvatureFamilyRequired =
  S3F2.universalMarkedCurvatureFamilyRequiredForCosmology

s3FreshDifferentiatedDecayTheoremRequired : Bool
s3FreshDifferentiatedDecayTheoremRequired =
  S3Source.freshDifferentiatedDecayTheoremRequired

s3IndependentHilbertInequalityRequired : Bool
s3IndependentHilbertInequalityRequired =
  S3Source.freshHilbertInequalityRequired

s3MarkedCoordinateAndUniformRadiusWeldRequired : Bool
s3MarkedCoordinateAndUniformRadiusWeldRequired =
  S3Source.selectedF2MarkedCoordinateAndUniformRadiusWeldRequired

s3GaugeLocalSemanticsRequired : Bool
s3GaugeLocalSemanticsRequired =
  S3Source.selectedF2GaugeLocalSemanticsRequired

------------------------------------------------------------------------
-- S3b: literal Eq.(1.71) realization + Lipschitz mesh convergence.
------------------------------------------------------------------------

s3LiteralEquation171FiniteRealizationRequired : Bool
s3LiteralEquation171FiniteRealizationRequired =
  S3Eq171.literalEquation171FiniteCarrierDensityIntegralRealizationRequired

s3AbstractEquation171CallbackSuffices : Bool
s3AbstractEquation171CallbackSuffices =
  S3Eq171.abstractEquation171CallbackAloneDeterminesLipschitzBound

s3IndependentOscillationVanishingRequired : Bool
s3IndependentOscillationVanishingRequired =
  Lipschitz.independentOscillationVanishingTheoremRequired

s3Equation171LipschitzCellBoundRequired : Bool
s3Equation171LipschitzCellBoundRequired =
  Lipschitz.remainingEquation171AnalyticWorkIsLipschitzCellBound

s3ProductHaarVanishingMeshRequired : Bool
s3ProductHaarVanishingMeshRequired =
  Lipschitz.remainingHaarPartitionWorkIsVanishingMesh

s3IndependentMassDiscrepancyConvergenceRequired : Bool
s3IndependentMassDiscrepancyConvergenceRequired =
  ExactMass.independentMassDiscrepancyVanishesRequired

s3SelectedStateEqualityRequired : Bool
s3SelectedStateEqualityRequired =
  S3Haar.separateSelectedStateEqualityRequired

s3CellCountGrowthRequired : Bool
s3CellCountGrowthRequired =
  S3Haar.massDiscrepancyOrCellCountGrowthRequired

------------------------------------------------------------------------
-- Retired debt.
------------------------------------------------------------------------

primitiveSignedCovarianceRequired : Bool
primitiveSignedCovarianceRequired = false

freeTraceFrameCalibrationRequired : Bool
freeTraceFrameCalibrationRequired = false

r129StressSourceEqualsF2SourceRequired : Bool
r129StressSourceEqualsF2SourceRequired = false

postHocCompletedF2EqualityRequired : Bool
postHocCompletedF2EqualityRequired = false

finiteDGammaR109TailRouteRequired : Bool
finiteDGammaR109TailRouteRequired = false

eq223VacuumGapRouteRequired : Bool
eq223VacuumGapRouteRequired = false

remainingAdapterDebt : Nat
remainingAdapterDebt = 0

preferredFrontierContainsOnlySourceMathematicsOrImportedAuthority : Bool
preferredFrontierContainsOnlySourceMathematicsOrImportedAuthority = true
