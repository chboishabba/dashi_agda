{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealBMinCutExact where

------------------------------------------------------------------------
-- CANONICAL PINNED-CMP119 REAL B MIN-CUT
--
-- Global policy:
--   Clay min-cut first; max-cut only inside the Clay-relevant induced graph.
--
-- At this point the preferred real CMP119/CMP116 B lane has only two
-- source/physics-bearing coordinates:
--
--   B-J    the published selected CMP116 J coordinate is the literal
--          normalized two-J source coordinate on the SAME CMP119 family;
--
--   B-env  the selected CMP116 source/tree envelope has the concrete
--          sourceAmplitude * exp(-mu d_latt) majorant.
--
-- Everything after those coordinates is already compiler/standard-owned:
-- normalized cumulant = connected covariance, physical scale conversion,
-- exp(-x) antitonicity, amplitude transport, and finite->continuum upper
-- closure.  This module composes those owners without introducing a new
-- analytic inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as App
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Cluster
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116PhysicalUpperExact as Upper
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact as ScaleCal
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

continuumPhysicalCovarianceBelowCalibratedUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      ScaleCarrier Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group twoJ source application expReal embedding}
    (calibration :
      ScaleCal.LiteralRealCMP116ScaleCalibration
        ScaleCarrier Volume Root SourceDirection Index
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
  ScaleCal.physicalExponentialUpper calibration index
continuumPhysicalCovarianceBelowCalibratedUpper calibration orderLimit index =
  Upper.continuumPhysicalCovarianceBelowUpper
    (ScaleCal.asPhysicalUpperInputs calibration orderLimit)
    index

------------------------------------------------------------------------
-- Proof-level boundary.
------------------------------------------------------------------------

pinnedCMP119RealBPostCoordinateCompilerLevel : ProofLevel
pinnedCMP119RealBPostCoordinateCompilerLevel = machineChecked

-- B-J: exact selected source-coordinate meaning.
pinnedCMP119RealBSelectedJCoordinateLevel : ProofLevel
pinnedCMP119RealBSelectedJCoordinateLevel =
  App.literalCMP116SelectedJCoordinateLevel

-- B-env: source/tree envelope -> concrete exponential majorant.
pinnedCMP119RealBSelectedEnvelopeLevel : ProofLevel
pinnedCMP119RealBSelectedEnvelopeLevel =
  ScaleCal.literalCMP116SelectedEnvelopeExponentialIdentificationLevel

-- No third Yang--Mills decay theorem is introduced by this owner.
pinnedCMP119RealBAdditionalAnalyticInequalityRequired : Bool
pinnedCMP119RealBAdditionalAnalyticInequalityRequired = false
