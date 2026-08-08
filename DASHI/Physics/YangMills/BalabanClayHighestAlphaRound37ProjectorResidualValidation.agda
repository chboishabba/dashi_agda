module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound37ProjectorResidualValidation where

------------------------------------------------------------------------
-- Cumulative Round Thirty Seven validation root.
--
-- Round 37 imports the complete Round-36 finite atom/selector lane and adds:
-- literal physical coordinate projectors, the actual four-bond plaquette
-- boundary projector, commuting triple-mask composition, a finite covector
-- spillover identity, same-object Noether residual reduction and assembly,
-- orientation reversal, the sixteen-atom centred probe, finite Rayleigh
-- certificates, strict owned RG margins, E8 root-data numerics and a typed
-- 196608 atlas.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalProjectorCompositionExact as Composition
import DASHI.Physics.YangMills.BalabanSelectedVariationProjectionSpilloverExact as Spillover
import DASHI.Physics.YangMills.BalabanSelectedVariationProjectedNoetherResidualExact as Noether
import DASHI.Physics.YangMills.BalabanSelectedVariationProjectedSelectorAssemblyExact as Assembly
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PlaquetteOrientationReversalExact as Reversal
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanWilsonSixteenAtomCentredProbeExact as Probe
import DASHI.Physics.YangMills.BalabanP33LiteralHessianSpectralCertificateExact as Spectral
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalStateDualTiltExact as Tilt
import DASHI.Physics.YangMills.BalabanP33StrictOwnedMarginExact as Margin
import DASHI.Physics.YangMills.BalabanE8QuantitativeRootDataExact as E8
import DASHI.Physics.YangMills.BalabanCommon196608AtlasExact as Atlas

open import Agda.Builtin.Equality using (_≡_)
import Agda.Builtin.Nat as Nat
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 1ℚ; _+_; _*_; _≤_; _/_)

physicalProjectorIdempotenceRegression :
  ∀ mask vector coordinate →
  Projector.physicalCoordinateProject mask
    (Projector.physicalCoordinateProject mask vector) coordinate
  ≡ Projector.physicalCoordinateProject mask vector coordinate
physicalProjectorIdempotenceRegression =
  Projector.physicalConstraintProjectorIdempotent

plaquetteBoundaryExtractorIsLocal :
  ∀ field plaquette →
  Projector.PhysicalConstraintProjectorImage
    (Boundary.plaquetteBoundaryMask plaquette)
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)
plaquetteBoundaryExtractorIsLocal =
  Boundary.rawPlaquetteSingletonExtractorLocal

tripleConstraintProjectorIdempotenceRegression :
  ∀ gauge tangent boundary vector coordinate →
  Composition.triplePhysicalConstraintProject gauge tangent boundary
    (Composition.triplePhysicalConstraintProject
      gauge tangent boundary vector)
    coordinate
  ≡ Composition.triplePhysicalConstraintProject
      gauge tangent boundary vector coordinate
tripleConstraintProjectorIdempotenceRegression =
  Composition.triplePhysicalConstraintProjectorIdempotent

projectedSpilloverBudgetRegression :
  ∀ {background field plaquette}
    (data : Spillover.ProjectionSpilloverData
      background field plaquette) →
  Spillover.projectedExtractionSpillover data
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge field plaquette
projectedSpilloverBudgetRegression =
  Spillover.projectedExtractionSpilloverUpper

projectedNoetherConstructionProducesRound36Witness :
  ∀ {background field plaquette} →
  Noether.ProjectedSingletonConstruction
    background field plaquette →
  Selector.SingletonExtractionWitness
    background field plaquette
projectedNoetherConstructionProducesRound36Witness =
  Noether.projectedConstructionToSingletonWitness

assembledAnalyticDataProducesRound36Witness :
  ∀ {background field plaquette} →
  Assembly.ProjectedSelectorAnalyticData
    background field plaquette →
  Selector.SingletonExtractionWitness
    background field plaquette
assembledAnalyticDataProducesRound36Witness =
  Assembly.analyticDataToSingletonExtractionWitness

orientationReversalPreservesWilsonScalar :
  ∀ value →
  Telescope.wilsonScalar (Reversal.reverseQuaternion value)
  ≡ Telescope.wilsonScalar value
orientationReversalPreservesWilsonScalar =
  Reversal.reverseWilsonScalarInvariant

uniformSixteenProbeRegression :
  ∀ weight base defects →
  Probe.sixteen
    * Probe.weightedSum16
        (Probe.constant16 weight)
        (Probe.addBase16 base defects)
  ≡ Probe.sum16 (Probe.constant16 weight)
      * (Probe.sixteen * base + Probe.sum16 defects)
uniformSixteenProbeRegression =
  Probe.uniformWeightsSeeOnlyAugmentation

maximalCoerciveCoreRegression :
  Margin.commonCore
    (Margin.maximalCoreCandidate (+ 1 / 32))
  ≡ + 1 / 32
maximalCoerciveCoreRegression =
  Margin.maximalUniformCoerciveCoreAttained (+ 1 / 32)

p33SpectralFloorRegression :
  ∀ {matrix vector eigenvalue} →
  Spectral.PhysicalQuadraticFloor
    matrix Spectral.p33OneThirtySecond →
  Spectral.PhysicalEigenpair matrix vector eigenvalue →
  Physical.physicalSU2CoordinateNormSq vector ≡ 1ℚ →
  Spectral.p33OneThirtySecond ≤ eigenvalue
p33SpectralFloorRegression =
  Spectral.p33NormalizedEigenvalueAtLeastOneThirtySecond

e8RankRootsDimensionRegression :
  Nat._+_ E8.e8Rank E8.e8RootCount ≡ E8.e8AdjointDimension
e8RankRootsDimensionRegression =
  E8.e8RankPlusRootsIsAdjointDimension

yangMillsAtlasChartRegression :
  Atlas.chartValue Atlas.yangMillsWilsonRadiusChart
  ≡ Atlas.common196608
yangMillsAtlasChartRegression = Atlas.yangMillsChartIs196608

phaseAtlasChartRegression :
  Atlas.chartValue Atlas.monsterPhaseChart
  ≡ Atlas.common196608
phaseAtlasChartRegression = Atlas.phaseChartIs196608

leechAtlasChartRegression :
  Atlas.chartValue Atlas.leechWeightTwoCoordinateChart
  ≡ Atlas.common196608
leechAtlasChartRegression = Atlas.leechChartIs196608
