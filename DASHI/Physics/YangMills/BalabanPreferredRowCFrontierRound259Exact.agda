{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRowCFrontierRound259Exact where

------------------------------------------------------------------------
-- ROUND259 / LEAST-PRIVILEGE ROW-C FRONTIER AFTER SAME-DENSITY INTROSPECTION
--
-- The historical Row-C surfaces over-counted several downstream consequences as
-- independent physical lemmas.  Current in-repo archaeology gives the shorter
-- dependency chain:
--
--   exact same-density compact-group Heat/Doob realization
--     + pointwise real CMP116 Hessian -> marked rational shell
--     + exact covariance -> marked first-gradient rational majorant
--     -> rational temporal debt (R257)
--
--   same literal Heat/Doob generator
--     + one weighted generator-row = CMP116 marked Hessian-row identification
--     -> every weighted Dyson power (existing compiler)
--
--   same-measure relaxation + same-generator finite speed
--     -> stochastic spatial envelope (existing Round70 compiler)
--     + one geometric-envelope shape payment
--     -> explicit connected clustering (R258).
--
-- No old temporal split inequality, spatial dynamic/static split, all-power
-- propagation theorem, or broad clustering record remains primitive here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact as Heat
import DASHI.Physics.YangMills.BalabanHeatDoobMarkedTemporalMajorizationRound257Exact as Temporal
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientCovarianceInstantiationRound102Exact as FirstCov
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as Spatial
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact as Stochastic
import DASHI.Physics.YangMills.BalabanStochasticSpatialEnvelopeToConnectedClusteringRound258Exact as Cluster
import DASHI.Physics.YangMills.BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact as HessianShell


data PreferredRowCLeaf259 : Set where
  literalSameDensityCompactGroupHeatExpectation : PreferredRowCLeaf259
  literalRealCMP116HessianToMarkedShell : PreferredRowCLeaf259
  literalExactCovarianceToMarkedFirstGradientMajorant : PreferredRowCLeaf259
  literalSameDensityWeightedGeneratorIsCMP116HessianRow : PreferredRowCLeaf259
  literalSameMeasureTemporalRelaxationAtBalancedTime : PreferredRowCLeaf259
  literalSameGeneratorFiniteSpeedAtBalancedTime : PreferredRowCLeaf259
  literalGeometricSpatialEnvelope : PreferredRowCLeaf259


data LeafState259 : Set where
  open closed : LeafState259

preferredRowCLeafState259 : PreferredRowCLeaf259 → LeafState259
preferredRowCLeafState259 literalSameDensityCompactGroupHeatExpectation = open
preferredRowCLeafState259 literalRealCMP116HessianToMarkedShell = open
preferredRowCLeafState259 literalExactCovarianceToMarkedFirstGradientMajorant = open
preferredRowCLeafState259 literalSameDensityWeightedGeneratorIsCMP116HessianRow = open
preferredRowCLeafState259 literalSameMeasureTemporalRelaxationAtBalancedTime = open
preferredRowCLeafState259 literalSameGeneratorFiniteSpeedAtBalancedTime = open
preferredRowCLeafState259 literalGeometricSpatialEnvelope = open

-- The key compiler/source levels are referenced from their canonical owners so
-- this frontier cannot drift into a second authority.
sameDensityHeatExpectationLevel : ProofLevel
sameDensityHeatExpectationLevel = Heat.sameDensityHeatExpectationPhysicalLevel

pointwiseHessianMarkedShellLevel : ProofLevel
pointwiseHessianMarkedShellLevel =
  HessianShell.literalCMP116PhysicalCompositeHessianShellIdentificationLevel

exactCovarianceMarkedFirstGradientLevel : ProofLevel
exactCovarianceMarkedFirstGradientLevel =
  FirstCov.literalCMP116FirstGradientHeatDoobIdentificationLevel

weightedGeneratorMarkedHessianRowLevel : ProofLevel
weightedGeneratorMarkedHessianRowLevel =
  Spatial.literalHeatDoobGeneratorIsCMP116HessianRowLevel

stochasticTemporalFiniteSpeedLevel : ProofLevel
stochasticTemporalFiniteSpeedLevel =
  Stochastic.physicalYMStochasticFiniteSpeedClusteringLevel

geometricSpatialEnvelopeLevel : ProofLevel
geometricSpatialEnvelopeLevel = Cluster.literalSameFamilyGeometricSpatialEnvelopeLevel

-- Closed consequences after the leaves above are inhabited.
temporalRealToRationalCompilerLevel : ProofLevel
temporalRealToRationalCompilerLevel = Temporal.markedTemporalRealToRationalCompilerLevel

spatialAllDysonPowersCompilerLevel : ProofLevel
spatialAllDysonPowersCompilerLevel = Spatial.sameObjectGeneratorRowToAllDysonPowerRowsLevel

connectedClusteringCompilerLevel : ProofLevel
connectedClusteringCompilerLevel = Cluster.stochasticEnvelopeToRound108ClusteringCompilerLevel

-- Historical broad objects remain available for compatibility, but are no
-- longer the preferred acquisition units.
round259RowCPhysicalClosure : Bool
round259RowCPhysicalClosure = false

round259RowCPhysicalClosureIsFalse : round259RowCPhysicalClosure ≡ false
round259RowCPhysicalClosureIsFalse = refl
