{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealR415ClusteringExact where

------------------------------------------------------------------------
-- R415 LITERAL MARKED EXPANSION -> CONTINUUM PHYSICAL CLUSTERING
--
-- This is the preferred post-R416 B consumer.
--
-- No free B-env inequality appears in this theorem.  Once the literal selected
-- R415 expansion is attached to the CMP116 source envelope/amplitude/decay
-- coordinates, R416 constructs the existing scale calibration and the pinned
-- B min-cut transports it all the way to the continuum CMP119 covariance.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as App
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Cluster
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealBMinCutExact as B
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionScaleCalibrationRound416Exact as R416
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

r415SelectedExpansionBuildsContinuumPhysicalClustering :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group twoJ source application expReal embedding}
    (calibration :
      R416.SelectedR415EnvelopeCalibration
        ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
        source
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.left application index))
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.right application index))
        (App.scaleAt application)
        (App.volumeAt application)
        expReal embedding)
    (orderLimit : Cluster.RealUpperClosedLimit sequenceLimit)
    (index : Index) →
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData a group))
    (App.left application index)
    (App.right application index)
  ≤ℝ
  DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact.physicalExponentialUpper
    (R416.asLiteralRealCMP116ScaleCalibration calibration)
    index
r415SelectedExpansionBuildsContinuumPhysicalClustering
    calibration orderLimit index =
  B.continuumPhysicalCovarianceBelowCalibratedUpper
    (R416.asLiteralRealCMP116ScaleCalibration calibration)
    orderLimit
    index

r415ToContinuumPhysicalClusteringCompilerLevel : ProofLevel
r415ToContinuumPhysicalClusteringCompilerLevel = machineChecked
