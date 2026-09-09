{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRowCFrontierRound262Exact where

------------------------------------------------------------------------
-- ROUND262 / ROW-C FRONTIER AFTER PHYSICAL-DECOUPLED COMPARISON INTROSPECTION
--
-- R259 correctly split absolute Hessian control into source comparison plus a
-- reference anchor.  R261 descends one level further into the comparison side.
-- The old single leaf
--
--   literalCMP116MarkedHessianComparison
--
-- is therefore no longer the least-privilege source coordinate.  Its compiler
-- path is now
--
--   literal physical CMP116 Hessian
--      == decoupled Cauchy coefficient                      [same-object weld]
--   + marked substituted-background boundary estimate      [source analysis]
--      -> real coefficient comparison                       [compiler]
--   + real source majorant <= embedded rational shell       [coarsening/weld]
--      -> rational comparison debt                          [compiler]
--   + reference-domain rational anchor                      [independent source]
--      -> absolute static Hessian rational majorant          [R260 compiler].
--
-- This file records that refinement only.  It does not claim any of the new
-- source-facing leaves are inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact as Heat
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDecoupledComparisonRound261Exact as Comparison
import DASHI.Physics.YangMills.BalabanCMP116AnchoredHessianMajorantRound260Exact as Anchor
import DASHI.Physics.YangMills.BalabanHeatDoobMarkedTemporalMajorizationRound257Exact as Temporal
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as Spatial
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact as Stochastic
import DASHI.Physics.YangMills.BalabanStochasticSpatialEnvelopeToConnectedClusteringRound258Exact as Cluster


data PreferredRowCLeaf262 : Set where
  literalSameDensityCompactGroupHeatExpectation : PreferredRowCLeaf262

  literalCMP116PhysicalDifferenceIsDecoupledCoefficient : PreferredRowCLeaf262
  literalCMP116MarkedSubstitutionBoundaryEstimate : PreferredRowCLeaf262
  literalCMP116RealMajorantToRationalHessianShell : PreferredRowCLeaf262
  literalReferenceHessianAnchorMajorant : PreferredRowCLeaf262

  literalExactCovarianceToMarkedFirstGradientMajorant : PreferredRowCLeaf262
  literalSameDensityWeightedGeneratorIsCMP116HessianRow : PreferredRowCLeaf262
  literalSameMeasureTemporalRelaxationAtBalancedTime : PreferredRowCLeaf262
  literalSameGeneratorFiniteSpeedAtBalancedTime : PreferredRowCLeaf262
  literalGeometricSpatialEnvelope : PreferredRowCLeaf262


data LeafState262 : Set where
  open closed : LeafState262

preferredRowCLeafState262 : PreferredRowCLeaf262 → LeafState262
preferredRowCLeafState262 literalSameDensityCompactGroupHeatExpectation = open
preferredRowCLeafState262 literalCMP116PhysicalDifferenceIsDecoupledCoefficient = open
preferredRowCLeafState262 literalCMP116MarkedSubstitutionBoundaryEstimate = open
preferredRowCLeafState262 literalCMP116RealMajorantToRationalHessianShell = open
preferredRowCLeafState262 literalReferenceHessianAnchorMajorant = open
preferredRowCLeafState262 literalExactCovarianceToMarkedFirstGradientMajorant = open
preferredRowCLeafState262 literalSameDensityWeightedGeneratorIsCMP116HessianRow = open
preferredRowCLeafState262 literalSameMeasureTemporalRelaxationAtBalancedTime = open
preferredRowCLeafState262 literalSameGeneratorFiniteSpeedAtBalancedTime = open
preferredRowCLeafState262 literalGeometricSpatialEnvelope = open

sameDensityHeatExpectationLevel : ProofLevel
sameDensityHeatExpectationLevel =
  Heat.literalCompactGroupHeatTiltExpectationRound108Level

physicalDifferenceCoefficientIdentityLevel : ProofLevel
physicalDifferenceCoefficientIdentityLevel =
  Comparison.physicalDifferenceCoefficientIdentityLevel

markedSubstitutionBoundaryEstimateLevel : ProofLevel
markedSubstitutionBoundaryEstimateLevel =
  Comparison.markedSubstitutionSourceEstimateLevel

realMajorantToRationalHessianShellLevel : ProofLevel
realMajorantToRationalHessianShellLevel =
  Comparison.realSourceMajorantToRationalShellLevel

referenceHessianAnchorLevel : ProofLevel
referenceHessianAnchorLevel = Anchor.referenceAnchorMajorizationLevel

exactCovarianceMarkedFirstGradientMajorizationLevel : ProofLevel
exactCovarianceMarkedFirstGradientMajorizationLevel =
  Temporal.literalHeatDoobCovarianceMarkedFirstGradientMajorizationLevel

weightedGeneratorMarkedHessianRowLevel : ProofLevel
weightedGeneratorMarkedHessianRowLevel =
  Spatial.literalHeatDoobGeneratorIsCMP116HessianRowLevel

stochasticTemporalAndFiniteSpeedLevel : ProofLevel
stochasticTemporalAndFiniteSpeedLevel =
  Stochastic.physicalYMStochasticFiniteSpeedClusteringLevel

geometricSpatialEnvelopeLevel : ProofLevel
geometricSpatialEnvelopeLevel = Cluster.literalSameFamilyGeometricSpatialEnvelopeLevel

------------------------------------------------------------------------
-- Compiler-owned consequences after source leaves are paid.
------------------------------------------------------------------------

physicalDecoupledComparisonCompilerLevel : ProofLevel
physicalDecoupledComparisonCompilerLevel =
  Comparison.physicalDecoupledComparisonCompilerLevel

anchoredAbsoluteHessianCompilerLevel : ProofLevel
anchoredAbsoluteHessianCompilerLevel = Anchor.anchoredHessianMajorantCompilerLevel

temporalRealToRationalCompilerLevel : ProofLevel
temporalRealToRationalCompilerLevel = Temporal.markedTemporalRealToRationalCompilerLevel

spatialAllDysonPowersCompilerLevel : ProofLevel
spatialAllDysonPowersCompilerLevel = Spatial.sameObjectGeneratorRowToAllDysonPowerRowsLevel

connectedClusteringCompilerLevel : ProofLevel
connectedClusteringCompilerLevel = Cluster.stochasticEnvelopeToRound108ClusteringCompilerLevel

round262RowCPhysicalClosure : Bool
round262RowCPhysicalClosure = false

round262RowCPhysicalClosureIsFalse : round262RowCPhysicalClosure ≡ false
round262RowCPhysicalClosureIsFalse = refl
