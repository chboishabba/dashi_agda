module DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination
import DASHI.Empirical.DarkDimensionPredictionQuantityAdapterExact as QuantityAdapter
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- SOURCE-PRECISION-AWARE QUANTITATIVE ENVELOPES
--
-- This owner separates source precision rather than flattening every number
-- into one prediction object:
--
--   * c' = 0.05 +/- 0.01 with c' <= approximately 0.2;
--   * effective Dark-Dimension radius around 1-30 micrometres;
--   * DAO abstract: qualitative "percent-level" amplitude;
--   * DAO published full text: numerical interval 0.005 <= A_D <= 0.025.
--
-- The abstract/full-text refinement is retained explicitly because source
-- version and inspected surface matter.  None of these retrospective/source
-- envelopes is thereby converted into a preregistered future forecast.
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- Canonical SI interval for the short-range-gravity / dark-dimension radius.
------------------------------------------------------------------------

record SIInterval (dimension : SI.Dimension) (scale : SI.DecimalScale) : Set where
  constructor siInterval
  field
    lower : SI.Quantity dimension scale
    upper : SI.Quantity dimension scale

open SIInterval public

darkDimensionRadiusLowerMicrometre : SI.Quantity SI.Length SI.microScale
darkDimensionRadiusLowerMicrometre = SI.posQ 1

darkDimensionRadiusUpperMicrometre : SI.Quantity SI.Length SI.microScale
darkDimensionRadiusUpperMicrometre = SI.posQ 30

darkDimensionRadiusEnvelope : SIInterval SI.Length SI.microScale
darkDimensionRadiusEnvelope =
  siInterval
    darkDimensionRadiusLowerMicrometre
    darkDimensionRadiusUpperMicrometre

lawSmithEtAl2024 : Source.AttributedSource
lawSmithEtAl2024 =
  Source.mkDOISource
    "Jamie A. P. Law-Smith; Georges Obied; Anirudh Prabhu; Cumrun Vafa"
    "Astrophysical constraints on decaying dark gravitons"
    "Journal of High Energy Physics 2024, 47"
    "2024"
    "10.1007/JHEP06(2024)047"
    "https://doi.org/10.1007/JHEP06(2024)047"
    Source.academicArticleSource
    "source for the natural effective-size interval around 1-30 micrometres in the decaying-dark-graviton Dark-Dimension scenario; this interval is not a laboratory detection claim"
    Source.publicAttribution

------------------------------------------------------------------------
-- Dimensionless evolving-dark-sector coupling coordinate.
------------------------------------------------------------------------

record RatioEstimate : Set where
  constructor ratioEstimate
  field
    central : Discrimination.DecimalRatio
    uncertainty : Discrimination.DecimalRatio
    externalUpperBound : Discrimination.DecimalRatio
    retrospectiveFit : Bool
    heldOutPrediction : Bool

open RatioEstimate public

bedroyaCPrimeEnvelope : RatioEstimate
bedroyaCPrimeEnvelope =
  ratioEstimate
    Discrimination.cPrimeBestFitFiveHundredths
    Discrimination.cPrimeUncertaintyOneHundredth
    Discrimination.cPrimeFifthForceUpperBoundTwoTenths
    true
    false

bedroyaSource : Source.AttributedSource
bedroyaSource = DarkDimension.bedroyaObiedVafaWu2026

------------------------------------------------------------------------
-- DAO precision boundary and source-version refinement.
------------------------------------------------------------------------

data AmplitudePrecision : Set where
  exactAmplitude : AmplitudePrecision
  intervalAmplitude : AmplitudePrecision
  qualitativeScaleAmplitude : AmplitudePrecision

data QualitativeAmplitudeBand : Set where
  percentLevelAmplitude : QualitativeAmplitudeBand

record DAOAmplitudeEnvelope : Set where
  constructor daoAmplitudeEnvelope
  field
    source : Source.AttributedSource
    precision : AmplitudePrecision
    qualitativeBand : QualitativeAmplitudeBand
    exactNumericalAmplitudeLocked : Bool
    futureFullShapeScrutinyNamed : Bool

open DAOAmplitudeEnvelope public

daoPercentLevelAmplitudeBand : DAOAmplitudeEnvelope
daoPercentLevelAmplitudeBand =
  daoAmplitudeEnvelope
    Discrimination.darkAcousticOscillationSource
    qualitativeScaleAmplitude
    percentLevelAmplitude
    false
    true

daoAbsoluteAmplitudeLower : Discrimination.DecimalRatio
daoAbsoluteAmplitudeLower = Discrimination.decimalRatio 5 1000

daoAbsoluteAmplitudeUpper : Discrimination.DecimalRatio
daoAbsoluteAmplitudeUpper = Discrimination.decimalRatio 25 1000

record DAOAmplitudeInterval : Set where
  constructor daoAmplitudeInterval
  field
    intervalSource : Source.AttributedSource
    lowerAbsoluteAmplitude : Discrimination.DecimalRatio
    upperAbsoluteAmplitude : Discrimination.DecimalRatio
    intervalPrecision : AmplitudePrecision
    sourceSurface : String

open DAOAmplitudeInterval public

publishedDAOAmplitudeInterval : DAOAmplitudeInterval
publishedDAOAmplitudeInterval =
  daoAmplitudeInterval
    Discrimination.darkAcousticOscillationSource
    daoAbsoluteAmplitudeLower
    daoAbsoluteAmplitudeUpper
    intervalAmplitude
    "published Physical Review D full text: physically interesting linear-spectrum DAO amplitude approximately 0.005-0.025"

record DAOAbstractToFullTextPrecisionRefinement : Set where
  constructor daoAbstractToFullTextPrecisionRefinement
  field
    abstractPrecision : AmplitudePrecision
    fullTextPrecision : AmplitudePrecision
    publicationDOI : String
    abstractCarriesOnlyQualitativeBand : Bool
    fullTextCarriesNumericalInterval : Bool

open DAOAbstractToFullTextPrecisionRefinement public

abstractToFullTextPrecisionRefinement : DAOAbstractToFullTextPrecisionRefinement
abstractToFullTextPrecisionRefinement =
  daoAbstractToFullTextPrecisionRefinement
    qualitativeScaleAmplitude
    intervalAmplitude
    "10.1103/y31p-9g5k"
    true
    true

------------------------------------------------------------------------
-- Cross-model numerical-separation status.
------------------------------------------------------------------------

record QuantitativeEnvelopeStatus : Set where
  constructor quantitativeEnvelopeStatus
  field
    darkDimensionRadiusRangeRecorded : Bool
    bedroyaCPrimeFitRecorded : Bool
    daoPercentLevelScaleRecorded : Bool
    daoPublishedAmplitudeIntervalRecorded : Bool
    daoExactAmplitudeRecorded : Bool
    sourceValuesFrozenAsProspectivePrediction : Bool
    crossModelNumericalSeparationLocked : Bool
    preregistrationIdentifierRecorded : Bool
    heldOutFutureComparisonPerformed : Bool

open QuantitativeEnvelopeStatus public

canonicalQuantitativeEnvelopeStatus : QuantitativeEnvelopeStatus
canonicalQuantitativeEnvelopeStatus =
  quantitativeEnvelopeStatus
    true
    true
    true
    true
    false
    false
    false
    false
    false

crossModelNumericalSeparationStillOpen :
  crossModelNumericalSeparationLocked canonicalQuantitativeEnvelopeStatus ≡ false
crossModelNumericalSeparationStillOpen = refl

prospectiveQuantitativeSeparationStillOpen :
  sourceValuesFrozenAsProspectivePrediction canonicalQuantitativeEnvelopeStatus ≡ false
prospectiveQuantitativeSeparationStillOpen = refl

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data QualitativeBandManufacturesExactAmplitude : Set where

data SourceEnvelopeEqualsLockedPrediction : Set where

qualitativeBandCannotManufactureExactAmplitude :
  QualitativeBandManufacturesExactAmplitude → ⊥
qualitativeBandCannotManufactureExactAmplitude ()

sourceEnvelopeDoesNotEqualLockedPrediction :
  SourceEnvelopeEqualsLockedPrediction → ⊥
sourceEnvelopeDoesNotEqualLockedPrediction ()

sourceEnvelopeDoesNotPayDASHIDerivedPrediction :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
sourceEnvelopeDoesNotPayDASHIDerivedPrediction =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

------------------------------------------------------------------------
-- SI -> GR/quantum prediction-quantity residual.
--
-- The generic signed-scale conversion remains deliberately unpaid.  The thin
-- Dark-Dimension adapter pays only the two positive micrometre endpoints by
-- encoding them as exact rational metres with decimalExponent = 0.
------------------------------------------------------------------------

record PredictionQuantityAdapterResidual : Set where
  constructor predictionQuantityAdapterResidual
  field
    canonicalSIQuantityAvailable : Bool
    predictionScaledQuantitySurfaceAvailable : Bool
    darkDimensionMicrometreEndpointAdapterAvailable : Bool
    genericSignedScaleConventionWelded : Bool
    genericPhysicalUnitCarrierWelded : Bool
    adapterScope : String

open PredictionQuantityAdapterResidual public

canonicalPredictionQuantityAdapterResidual : PredictionQuantityAdapterResidual
canonicalPredictionQuantityAdapterResidual =
  predictionQuantityAdapterResidual
    true
    true
    true
    false
    false
    "the Dark-Dimension 1-30 micrometre endpoints have an exact rational-metre bridge into GRQuantumPredictionProtocol.ScaledQuantity; a generic signed DecimalScale/PhysicalUnit conversion law remains unpaid"

microRadiusLowerPredictionBridge : QuantityAdapter.ExactMicrometrePredictionBridge 1
microRadiusLowerPredictionBridge = QuantityAdapter.microRadiusLowerBridge

microRadiusUpperPredictionBridge : QuantityAdapter.ExactMicrometrePredictionBridge 30
microRadiusUpperPredictionBridge = QuantityAdapter.microRadiusUpperBridge

predictionQuantityAdapterAvailableButSeparationStillOpen :
  crossModelNumericalSeparationLocked canonicalQuantitativeEnvelopeStatus ≡ false
predictionQuantityAdapterAvailableButSeparationStillOpen =
  crossModelNumericalSeparationStillOpen

genericSignedScaleConventionStillOpen :
  genericSignedScaleConventionWelded canonicalPredictionQuantityAdapterResidual ≡ false
genericSignedScaleConventionStillOpen = refl

genericPhysicalUnitWeldStillOpen :
  genericPhysicalUnitCarrierWelded canonicalPredictionQuantityAdapterResidual ≡ false
genericPhysicalUnitWeldStillOpen = refl

------------------------------------------------------------------------
-- Source coordinates retained explicitly.  Citation imports neither proof nor
-- framework authority through AttributedSourceCore.
------------------------------------------------------------------------

bedroyaDOI : String
bedroyaDOI = "10.1103/1rsq-cv2m"

daoDOI : String
daoDOI = "10.1103/y31p-9g5k"

lawSmithDOI : String
lawSmithDOI = "10.1007/JHEP06(2024)047"
