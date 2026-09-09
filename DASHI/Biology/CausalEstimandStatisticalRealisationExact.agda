module DASHI.Biology.CausalEstimandStatisticalRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Core.StatisticalEvidenceCore as StatisticalCore
import DASHI.Statistics.ConfidenceIntervalRegionEvidenceExact as CI
import DASHI.Statistics.HypothesisRegionGeometryExact as Region
import DASHI.Statistics.StandardConfidenceIntervalInterpretationExact as StandardCI

------------------------------------------------------------------------
-- CAUSAL ESTIMAND -> ESTIMATOR -> ESTIMATE -> UNCERTAINTY REALISATION
--
-- Identification and estimand have already been separated upstream.  This
-- owner adds the next statistical coordinates without inventing a probability
-- calculus.  Sampling law, estimator-target semantics, uncertainty semantics,
-- and interval coverage are all application-supplied receipts.
------------------------------------------------------------------------

record EstimatorProcedure
    (estimand : Estimand.CausalEffectEstimand) : Set₁ where
  constructor estimator-procedure
  field
    Sample Estimate : Set

    estimator : Sample → Estimate

    SamplingLaw : Set
    samplingLawReceipt : SamplingLaw

    TargetsEstimand : Estimate → Estimand.CausalEffectEstimand → Set
    estimatorTargetsEstimand :
      (sample : Sample) →
      TargetsEstimand (estimator sample) estimand

    estimatorReference : String
    samplingReference : String
    targetReference : String

open EstimatorProcedure public

record RealisedEstimate
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : EstimatorProcedure estimand) : Set₁ where
  constructor realised-estimate
  field
    sample : Sample procedure
    estimate : Estimate procedure
    estimateIsEstimatorOutput : estimate ≡ estimator procedure sample
    sampleProvenanceReference : String
    estimateReference : String

open RealisedEstimate public

------------------------------------------------------------------------
-- Uncertainty is not identified with probability, standard error, confidence
-- interval, posterior width, or any one numerical carrier.  Applications state
-- their uncertainty semantics explicitly.
------------------------------------------------------------------------

record UncertaintyProcedure
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : EstimatorProcedure estimand) : Set₁ where
  constructor uncertainty-procedure
  field
    Uncertainty : Set
    uncertaintyOf : Sample procedure → Uncertainty

    UncertaintyProperty : Sample procedure → Uncertainty → Set
    uncertaintySound :
      (sample : Sample procedure) →
      UncertaintyProperty sample (uncertaintyOf sample)

    uncertaintyReference : String
    calibrationReference : String

open UncertaintyProcedure public

record EstimateWithUncertainty
    {estimand : Estimand.CausalEffectEstimand}
    {procedure : EstimatorProcedure estimand}
    (uncertaintyProcedure : UncertaintyProcedure procedure) : Set₁ where
  constructor estimate-with-uncertainty
  field
    realised : RealisedEstimate procedure
    uncertainty : Uncertainty uncertaintyProcedure
    uncertaintyMatchesSample :
      uncertainty
      ≡ uncertaintyOf uncertaintyProcedure (sample realised)
    reportingReference : String

open EstimateWithUncertainty public

------------------------------------------------------------------------
-- Confidence-interval realization.
--
-- This reuses the existing interval geometry.  A coverage theorem is not
-- manufactured by the mere existence of interval endpoints; the application
-- supplies a confidence procedure plus its coverage receipt.
------------------------------------------------------------------------

record ConfidenceIntervalEstimatorRealisation
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : EstimatorProcedure estimand) : Set₁ where
  constructor confidence-interval-estimator-realisation
  field
    Parameter : Set
    order : CI.OrderedIntervalGeometry Parameter

    parameterOfEstimate : Estimate procedure → Parameter
    intervalOfSample : Sample procedure → CI.ConfidenceInterval order

    CoverageProperty : Sample procedure → Set
    coverageReceipt :
      (sample : Sample procedure) → CoverageProperty sample

    intervalProcedureReference : String
    coverageReference : String
    parameterScaleReference : String

open ConfidenceIntervalEstimatorRealisation public

record RegionInterpretedEstimate
    {estimand : Estimand.CausalEffectEstimand}
    {procedure : EstimatorProcedure estimand}
    (intervalProcedure : ConfidenceIntervalEstimatorRealisation procedure) : Set₁ where
  constructor region-interpreted-estimate
  field
    geometry : Region.HypothesisRegionGeometry
      (Parameter intervalProcedure)

    sample : Sample procedure

    intervalEvidence :
      CI.IntervalRegionEvidence geometry
        (intervalOfSample intervalProcedure sample)

    interpretationReference : String

open RegionInterpretedEstimate public

------------------------------------------------------------------------
-- Canonical statistical-evidence boundary reuse.
------------------------------------------------------------------------

statisticalEvidenceBoundary : StatisticalCore.StatisticalEvidenceReceipt
  StatisticalCore.canonicalStatisticalEvidenceSurface
statisticalEvidenceBoundary = StatisticalCore.canonicalStatisticalEvidenceReceipt

probabilityRemainsDistinctFromStatisticalEvidence :
  StatisticalCore.probabilityDistinctFromStatistical
    StatisticalCore.canonicalStatisticalEvidenceSurface
  ≡ true
probabilityRemainsDistinctFromStatisticalEvidence =
  StatisticalCore.statisticalEvidenceProbabilityDistinctFromStatisticalIsTrue

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data EstimandMeansEstimatorPermission : Set where

data EstimatorMeansEstimateWithoutSamplePermission : Set where

data EstimateMeansTruthPermission : Set where

data UncertaintyMeansConfidenceIntervalPermission : Set where

data ConfidenceIntervalMeansCoveragePermission : Set where

data IdentifiedEstimandMeansUnbiasedEstimatorPermission : Set where

data NarrowIntervalMeansCausalIdentificationPermission : Set where

data StatisticalEstimateMeansUniversalTransportPermission : Set where

data StatisticalEvidenceMeansProbabilityPermission : Set where

estimandDoesNotDetermineEstimator : EstimandMeansEstimatorPermission → ⊥
estimandDoesNotDetermineEstimator ()

estimatorNeedsRealisedSample : EstimatorMeansEstimateWithoutSamplePermission → ⊥
estimatorNeedsRealisedSample ()

estimateDoesNotBecomeTruth : EstimateMeansTruthPermission → ⊥
estimateDoesNotBecomeTruth ()

uncertaintyDoesNotDefinitionallyMeanConfidenceInterval :
  UncertaintyMeansConfidenceIntervalPermission → ⊥
uncertaintyDoesNotDefinitionallyMeanConfidenceInterval ()

intervalEndpointsDoNotManufactureCoverage :
  ConfidenceIntervalMeansCoveragePermission → ⊥
intervalEndpointsDoNotManufactureCoverage ()

identifiedEstimandDoesNotManufactureUnbiasedEstimator :
  IdentifiedEstimandMeansUnbiasedEstimatorPermission → ⊥
identifiedEstimandDoesNotManufactureUnbiasedEstimator ()

narrowIntervalDoesNotIdentifyCause :
  NarrowIntervalMeansCausalIdentificationPermission → ⊥
narrowIntervalDoesNotIdentifyCause ()

statisticalEstimateDoesNotAutomaticallyTransport :
  StatisticalEstimateMeansUniversalTransportPermission → ⊥
statisticalEstimateDoesNotAutomaticallyTransport ()

statisticalEvidenceDoesNotDefinitionallyBecomeProbability :
  StatisticalEvidenceMeansProbabilityPermission → ⊥
statisticalEvidenceDoesNotDefinitionallyBecomeProbability ()

record CausalEstimandStatisticalRealisationBoundary : Set where
  constructor causal-estimand-statistical-realisation-boundary
  field
    estimandEstimatorEstimateUncertaintyRemainDistinct : Bool
    realisedEstimateRequiresSample : Bool
    samplingLawRequiresReceipt : Bool
    uncertaintyRequiresCalibrationReceipt : Bool
    confidenceIntervalCoverageRequiresReceipt : Bool
    intervalGeometryMayBeInterpretedSeparately : Bool
    narrowIntervalAutomaticallyIdentifiesCause : Bool
    estimateAutomaticallyEqualsTruth : Bool
    statisticalEvidenceDefinitionallyEqualsProbability : Bool
    probabilityCalculusInventedHere : Bool

canonicalCausalEstimandStatisticalRealisationBoundary :
  CausalEstimandStatisticalRealisationBoundary
canonicalCausalEstimandStatisticalRealisationBoundary =
  causal-estimand-statistical-realisation-boundary
    true true true true true true false false false false
