{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261007VExact where

------------------------------------------------------------------------
-- OVERLAY V / 2026-10-07: POST-UNIQUENESS / SELECTED-F2 / EXACT-HAAR CUT.
--
-- This supersedes U as the preferred accounting surface.
--
-- S1: background equivariance is DERIVED from uniqueness of the constrained
--     variational minimizer. The source payment is concrete invariance of the
--     action/constraint/regular gauge for the literal B4 generators.
--
-- S2: once the renormalized Hilbert/Weyl identity is stated on the exact
--     stress/F2 operator pair, authority-record instantiation is compiler-only.
--
-- S3a: the route consumes ONE selected marked F2 source, not a universal
--      curvature-polynomial family. Nuclear completion is compiler-owned.
--
-- S3b: exact Haar masses erase discrepancy. Direct oscillation convergence is
--      also not primitive: a uniform Eq.(1.71) Lipschitz cell bound plus a
--      vanishing product-Haar mesh compiles to oscillation -> 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanBackgroundMinimizerSymmetryNaturalityExact as S1
import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact as S2
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact as S3F2
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateMassWeightedHaarExact as S3Haar
import DASHI.Physics.Foundations.CMP119CosmologyP3ExactMassOscillationOnlyExact as ExactMass
import DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerExact as Lipschitz

------------------------------------------------------------------------
-- Terminal theorem accounting.
------------------------------------------------------------------------

remainingNovelSourceTheoremCount : Nat
remainingNovelSourceTheoremCount = 3

remainingStandardImportedTheoremCount : Nat
remainingStandardImportedTheoremCount = 1

remainingPreferredTheoremCount : Nat
remainingPreferredTheoremCount = 4

-- S1 source theorem package: instantiate the variational problem on the literal
-- CMP109/116 carrier and prove B4 invariance of its defining data.
s1ConcreteVariationalB4InvarianceRequired : Bool
s1ConcreteVariationalB4InvarianceRequired = true

s1PrimitiveBackgroundEquivarianceRequired : Bool
s1PrimitiveBackgroundEquivarianceRequired =
  S1.primitiveSelectedBackgroundEquivarianceRequired

s1NaturalityCompilerClosedOnceInvariant : Bool
s1NaturalityCompilerClosedOnceInvariant =
  S1.backgroundNaturalityFollowsFromInvariantVariationalProblem

-- S2 source theorem: the standard renormalized operator Ward identity on the
-- exact pair. No separate authority-record instantiation remains.
s2ExactRenormalizedOperatorIdentityRequired : Bool
s2ExactRenormalizedOperatorIdentityRequired =
  S2.remainingR2WorkIsExactRenormalizedOperatorIdentity

s2AuthorityRecordInstantiationRequired : Bool
s2AuthorityRecordInstantiationRequired =
  S2.remainingR2WorkIsInstantiationOfStandardWardAuthority

-- S3a source theorem package: construct exactly one selected marked F2 source
-- on the completed state. The Hilbert estimate itself has been reduced further
-- to literal differentiated-source coefficient-energy control.
s3SelectedMarkedF2SourceRequired : Bool
s3SelectedMarkedF2SourceRequired =
  S3F2.remainingSelectedF2SourceWorkIsPhysicalMarkedSourceDataAndSemantics

s3UniversalMarkedCurvatureFamilyRequired : Bool
s3UniversalMarkedCurvatureFamilyRequired =
  S3F2.universalMarkedCurvatureFamilyRequiredForCosmology

-- S3b source theorem package: prove an Eq.(1.71) Lipschitz cell estimate and
-- construct the product-Haar refinement with vanishing mesh. Their composition
-- supplies the old oscillation-vanishing field automatically.
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

preferredFrontierContainsOnlySourceMathematicsOrImportedWardTheorem : Bool
preferredFrontierContainsOnlySourceMathematicsOrImportedWardTheorem = true
